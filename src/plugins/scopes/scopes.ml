open Lustre_types 
open Corelang 
open Machine_code_types
open Machine_code_common

(* (variable, node name, node instance) *)
type scope_t = (var_decl * string * string option) list * var_decl

(* Scope to string list *)
let scope_to_sl ((sl, v) : scope_t) : string list=
  List.fold_right (
    fun (v, nodename, _) accu -> 
      v.var_id :: nodename :: accu
  ) sl [v.var_id]


let rec compute_scopes ?(first=true) prog root_node : scope_t list =
  let compute_scopes = compute_scopes ~first:false in
  (* Format.eprintf "Compute scope of %s@." main_node; *)
  try
    let node =  get_node root_node prog in    
    let all_vars = node.node_inputs @ node.node_locals @  node.node_outputs in
    let local_vars = if first then
                       node.node_locals
                     else
                       node.node_inputs @ node.node_locals in
    let local_scopes = List.map (fun x -> [], x) local_vars  in
    let sub_scopes =
      let sub_nodes =
	List.fold_left 
	  (fun res s -> 
	    match s with 
	    | Eq ({ eq_rhs ={ expr_desc = Expr_appl (nodeid, _, _); _}; _ } as eq) -> 
	      (* Obtaining the var_del associated to the first var of eq_lhs *)
	      (
		try
		  let query v = v.var_id = List.hd eq.eq_lhs in
		  let vid = List.find query all_vars in
		  (nodeid, vid)::res
		with Not_found -> Format.eprintf "eq=%a@.local_vars=%a@." Printers.pp_node_eq eq (Utils.fprintf_list ~sep:"," Printers.pp_var) local_vars; assert false 
	      )
	    | Eq _ -> res
	    | _ -> assert false (* TODO deal with Automaton *)
	  ) [] node.node_stmts
      in
      List.map (fun (nodeid, vid) ->
	let scopes = compute_scopes prog nodeid in
	List.map (fun (sl,v) -> (vid, nodeid, None)::sl, v) scopes (* instances are not yet known, hence the None *)
      ) sub_nodes
    in
    local_scopes @ (List.flatten sub_scopes) 
  with Not_found ->  []


let print_scopes =
  Utils.fprintf_list ~sep:"@ " 
    (fun fmt ((_, v) as s) -> Format.fprintf fmt "%a: %a" 
      (Utils.fprintf_list ~sep:"." Format.pp_print_string )(scope_to_sl s)
      Types.print_ty v.var_type)
    
     
    

(* let print_path fmt p =  *)
(*   Utils.fprintf_list ~sep:"." (fun fmt (id, _) -> Format.pp_print_string fmt id) fmt p *)

let get_node_vdecl_of_name name node =
  try
    List.find 
      (fun v -> v.var_id = name) 
      (node.node_inputs  @ node.node_outputs  @ node.node_locals ) 
  with Not_found -> 
    Format.eprintf "Cannot find variable %s in node %s@." name node.node_id;
    assert false

let rec get_path prog machines node id_list accu =
  let get_path = get_path prog machines in
  match id_list, accu with
  | [flow], [] ->  (* Special treatment of first level flow: node is here main_node *)
     let flow_var = get_node_vdecl_of_name flow node in
     [], flow_var, node.node_id
  | [id], (_, last_node, _)::_ -> (* last item, it should denote a local
				       memory variable (local var, memory or input *)
     let id_vdecl = 
       get_node_vdecl_of_name id (get_node last_node prog) 
     in
     List.rev accu, id_vdecl, last_node
  | varid::nodename::id_list_tl, _ -> (
    let e_machine = get_machine node.node_id machines in 
    (* Format.eprintf "Looking for def %s in call %s in machine %a@."  *)
    (* 	varid nodename *)
    (* 	Machine_code.pp_machine e_machine; *)
    let find_var = (fun v -> v.var_id = varid) in
    let instance = 
      List.find 
	(fun i -> match get_instr_desc i with 
	          | MStep(p, o, _) -> List.exists find_var p 
	          | _ -> false
	) 
	e_machine.mstep.step_instrs 
    in
    try
      let variable, instance_node, instance_id = 
	match get_instr_desc instance with 
	| MStep(p, o, _) -> 
	   (* Format.eprintf "Looking for machine %s@.@?" o; *)
	   let o_fun, _ = List.assoc o e_machine.mcalls in
	   if node_name o_fun = nodename then
	     List.hd p, o_fun, o 
	   else 
	     assert false
	| _ -> assert false
      in
      let next_node = node_of_top instance_node in
      let accu = (variable, nodename, Some instance_id)::accu in
      (* Format.eprintf "Calling get path on %s@.@?" next_node.node_id; *)
      get_path next_node id_list_tl accu
    with Not_found -> Format.eprintf "toto@."; assert false
  )
  | _ -> assert false

    
let check_scope all_scopes  =
  let all_scopes_as_sl = List.map scope_to_sl all_scopes in
  fun prog machines main_node_name sl ->
  if not (List.mem sl all_scopes_as_sl) then (
    Format.eprintf "%s is an invalid scope.@." (String.concat "." sl);
    exit 1
  )
  else (
    (* Format.eprintf "@.@.Required path: %s@." (String.concat "." sl) ;  *)
    let main_node = get_node main_node_name prog in
    let path, flow, mid = get_path prog machines main_node sl [] in
    (* Format.eprintf "computed path: %a.%s@." print_path path flow.var_id; *)
    path, flow, mid
  )


                                                                
(* Build the two maps 
   - (scope_name, variable)
   - (machine_name, list of selected variables)
 *)
let check_scopes main_node_name prog machines all_scopes scopes =
  let check_scope = check_scope all_scopes prog machines in
  List.fold_left
    (fun (accu_sl, accu_m) sl ->
      let path, flow, mid = check_scope main_node_name sl in
      let accu_sl = (sl, (path, flow))::accu_sl in
      let accu_m =
        let flow_id = flow.var_id in
        if List.mem_assoc mid accu_m then
          (mid, flow_id::(List.assoc mid accu_m)) :: 
            (List.remove_assoc mid accu_m)
        else
          (mid, [flow_id])::accu_m
      in
      accu_sl, accu_m
    ) ([], []) scopes
  
  


let scope_var_name vid =  vid ^ "__scope"

(**********************************************************************)
(* The following three functions are used in the main function to print
   the value of the new memories, storing scopes values               *)
(**********************************************************************)

(* TODO: recuperer le type de "flow" et appeler le print correspondant 
   iterer sur path pour construire la suite des xx_mem._reg.yy_mem._reg......flow
par ex main_mem->n8->n9->_reg.flow
*)
let extract_scopes_defs scopes =
  let rec scope_path_name (path, flow) accu = 
    match path with 
    | [] -> accu ^ "_reg." ^ (scope_var_name flow.var_id), flow
    | (_, _, Some instance_id)::tl -> scope_path_name (tl, flow) ( accu ^ instance_id ^ "->" ) 
    | _ -> assert false
  in
  let scopes_vars = 
    List.map 
      (fun (sl, scope) -> 
	String.concat "." sl, scope_path_name scope "main_mem.") 
      scopes 
  in
  scopes_vars
  
let pp_scopes_files basename mname fmt scopes =
  let scopes_vars = extract_scopes_defs scopes in
  List.iteri (fun idx  _(*(id, (var_path, var))*)  ->
      C_backend_common.pp_file_decl fmt "out_scopes" idx)
    scopes_vars;
  Format.fprintf fmt "@[<v 2>if (traces) {@ ";
  List.iteri (fun idx  (id, (var_path, var))  ->
      let file = C_backend_common.pp_file_open fmt "out_scopes" idx in
      Format.fprintf fmt
        "fprintf(%s, \"# scope: %s\\n\");@ "
        file id;
      Format.fprintf fmt
        "fprintf(%s, \"# node: %s\\n\");@ "
        file (Utils.desome var.var_parent_nodeid);
      Format.fprintf fmt
        "fprintf(%s, \"# variable: %s\\n\");@ "
        file var.var_id
    ) scopes_vars;
  Format.fprintf fmt "@]}@ "
    
  
let pp_scopes fmt scopes = 
  let scopes_vars = extract_scopes_defs scopes in
  List.iteri (fun idx (id, (var_path, var)) ->
    Format.fprintf fmt "@ %t;" 
      (fun fmt -> C_backend_common.print_put_var fmt
                    ("_scopes" ^ string_of_int (idx+1))
                    id (*var*) var.var_type var_path)
  ) scopes_vars

(**********************************************************************)
                        
let update_machine main_node machine scopes =
  let stateassign (vdecl_mem, vdecl_orig) =
    mkinstr 
    (MStateAssign (vdecl_mem, mk_val (Var vdecl_orig) vdecl_orig.var_type))
  in
  let selection =
    (* We only register inputs for non root node *)
    (if machine.mname.node_id = main_node then
      []
    else
      machine.mstep.step_inputs
    )
    (* @ machine.mstep.step_outputs   *)
    @ machine.mmemory 
    @ machine.mstep.step_locals
  in
  let selection = List.filter (fun v -> List.exists (fun vid -> vid = v.var_id) scopes) selection in
  let new_mems = List.map (fun v ->
                     (* We could copy the variable but then we need to update its type 
                        let new_v = copy_var_decl v in
                      *)
                     let new_v = { v with var_id = scope_var_name v.var_id }  in
                     new_v, v
                   ) selection
  in
  { machine with
    mmemory = machine.mmemory @ (List.map fst new_mems);
    mstep = { 
      machine.mstep with 
        step_instrs = machine.mstep.step_instrs
        @ (mkinstr (MComment "Registering all flows"))::(List.map stateassign new_mems)
          
    }
  }
    
let rec is_valid_path path nodename prog machines =
  let nodescopes = compute_scopes prog nodename in
  let m = get_machine nodename machines in
  match path with
  | [] -> assert false
  | [vid] -> let res = List.exists (fun v -> v.var_id = vid) (m.mmemory @ m.mstep.step_inputs @ m.mstep.step_locals) in
	     (* if not res then  *)
	     (* 	 Format.eprintf "Variable %s cannot be found in machine %s@.Local vars are %a@." vid m.mname.node_id *)
	     (* 	   (Utils.fprintf_list ~sep:", " Printers.pp_var) (m.mmemory @ m.mstep.step_inputs @ m.mstep.step_locals) *)
	     (* ; *)
	     res
	     
  | inst::nodename::path' -> (* We use the scopes computed on the prog artifact *)
     (* Format.eprintf "Path is %a@ Local scopes: @[<v>%a@ @]@."  *)
     (* 	(Utils.fprintf_list ~sep:"." Format.pp_print_string) path *)
     (* 	(Utils.fprintf_list ~sep:";@ " *)
     (* 	   (fun fmt scope ->  *)
     (* 	     Utils.fprintf_list ~sep:"." Format.pp_print_string fmt (scope_to_sl scope)) *)
     (* 	)  *)
     (* 	nodescopes; *)
     if List.mem path (List.map scope_to_sl nodescopes) then (
       (* Format.eprintf "Valid local path, checking underneath@."; *)
       is_valid_path path' nodename prog machines
     )
     else
       false

      (* let instok = List.exists (fun (inst', node) -> inst' = inst) m.minstances in *)
      (* if not instok then Format.eprintf "inst = %s@." inst; *)
      (* instok &&  *)
      (* let instnode = fst (snd (List.find (fun (inst', node) -> inst' = inst) m.minstances)) in *)
      (* is_valid_path path' (Corelang.node_of_top instnode).node_id prog machines *)



(****************************************************)
      
let scopes_def : string list list ref = ref []
let inputs = ref []

let option_show_scopes = ref false
let option_scopes = ref false
let option_all_scopes = ref false
(* let option_mems_scopes = ref false 
 * let option_input_scopes = ref false *)

let scopes_map : (Lustre_types.ident list  * scope_t) list ref  = ref []
      
let process_scopes main_node prog machines =
  let all_scopes = compute_scopes prog !Options.main_node in
  let selected_scopes = if !option_all_scopes then
	                  List.map (fun s -> scope_to_sl s) all_scopes
                        else
	                  !scopes_def
  in
  (* Making sure all scopes are defined and were not removed by various
       optmizationq *)
  let selected_scopes = 
    List.filter 
      (fun sl -> 
	let res = is_valid_path sl main_node prog machines in
	if not res then
	  Format.eprintf "Scope %a is cancelled due to variable removal@." (Utils.fprintf_list ~sep:"." Format.pp_print_string) sl; 
	res
      ) 
      selected_scopes 
  in
  let scopes_map', machines_scopes = check_scopes main_node prog machines all_scopes selected_scopes in
  scopes_map := scopes_map';
  (* Each machine is updated with fresh memories and declared as stateful  *)
  let machines = List.map (fun m ->
                     let mid = m.mname.node_id in
                     if List.mem_assoc mid machines_scopes then
                       let machine_scopes = List.assoc mid machines_scopes in
                       update_machine main_node m machine_scopes
                     else
                       m) machines in
  machines

let activate () = 
  option_scopes := true;
  Options.optimization := 0; (* no optimization *)
  ()
  
let register_scopes s = 
  activate ();
  option_all_scopes:=false; 
  let scope_list = Str.split (Str.regexp ", *") s in
  let scope_list = List.map (fun scope -> Str.split (Str.regexp "\\.") scope) scope_list in
  scopes_def := scope_list

let register_inputs s = 
  activate ();
  let input_list = Str.split (Str.regexp "[;]") s in
  let input_list = List.map (fun s -> match Str.split (Str.regexp "=") s with | [v;e] -> v, e | _ -> raise (Invalid_argument ("Input list error: " ^ s))) input_list in
  let input_list = List.map (fun (v, e) -> v, Str.split (Str.regexp "[;]") e) input_list in
  inputs := input_list

let register_all_scopes () =
  activate ();
  option_all_scopes:= true
  
module Plugin : (
  sig
    include PluginType.PluginType
    val show_scopes: unit -> bool
    end) =
  struct
    include PluginType.Default
    let name = "scopes"
    let is_active () = 
      !option_scopes || !option_show_scopes || !option_all_scopes
    (* || !option_mem_scopes || !option_input_scopes *)
      
    let show_scopes () = 
      !option_show_scopes && (
        Compiler_common.check_main ();
        true)

    let usage fmt =
      let open Format in
      fprintf fmt "@[<hov 0>Scopes@ enrich@ the@ internal@ memories@ to@ record@ all@ or@ a@ selection@ of@ internals.@ In@ conjunction@ with@ the@ trace@ option@ of@ the@ produced@ binary@ it@ can@ also@ record@ these@ flow@ values@ within@ separated@ log@ files.@]@ @ ";
      fprintf fmt "Options are:@ "
    
    let options = [
        "-select", Arg.String register_scopes, "specifies which variables to log";
        "-input", Arg.String register_inputs, "specifies the simulation input";
        "-show-possible-scopes", Arg.Set option_show_scopes, "list possible variables to log";
        "-select-all", Arg.Unit register_all_scopes, "select all possible variables to log";
(* "-select-mems", Arg.Set option_mems_scopes, "select all memory variables to log";
 * "-select-inputs", Arg.Set option_input_scopes, "select all input variables to log"; *)
      ]

  let activate = activate

  let check_force_stateful () = is_active()

  let refine_machine_code prog machine_code =
    if show_scopes () then
      begin
	let all_scopes = compute_scopes prog !Options.main_node in
        (* Printing scopes *)
        if !Options.verbose_level >= 1 then 
	  Format.printf "Possible scopes are:@ ";
	Format.printf "@[<v 0>%a@ @]@.@?" print_scopes all_scopes;
	exit 0
      end;
    if is_active () then
      process_scopes !Options.main_node prog machine_code
    else
      machine_code
	


  let c_backend_main_loop_body_suffix fmt () =
    if is_active () then
      begin
	Format.fprintf fmt "@ %a" pp_scopes !scopes_map 
      end  

  let c_backend_main_loop_body_prefix basename mname fmt () =
    if is_active () then
      begin
	Format.fprintf fmt "@ %a" (pp_scopes_files basename mname) !scopes_map 
      end  


end
    
(* Local Variables: *)
(* compile-command:"make -C ../.." *)
(* End: *)
