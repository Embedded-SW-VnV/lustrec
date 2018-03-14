open LustreSpec
open Machine_code
open Format
open Horn_backend_common
open Horn_backend
   
let active = ref false
let ctx = ref (Z3.mk_context [])

let bool_sort = Z3.Boolean.mk_sort !ctx
let int_sort = Z3.Arithmetic.Integer.mk_sort !ctx
let real_sort = Z3.Arithmetic.Real.mk_sort !ctx

let const_sorts = Hashtbl.create 13
let get_const_sort ty_name =
  Hashtbl.find const_sorts ty_name

let decl_sorts () =
  Hashtbl.iter (fun typ decl ->
    match typ with
    | Tydec_const var ->
      (match decl.top_decl_desc with
      | TypeDef tdef -> (
	match tdef.tydef_desc with
	| Tydec_enum tl ->
	  let new_sort = Z3.Enumeration.mk_sort_s !ctx var tl in
          Hashtbl.add const_sorts var new_sort
	| _ -> assert false
      )
      | _ -> assert false
      )
    | _        -> ()) Corelang.type_table


let rec type_to_sort t =
  if Types.is_bool_type t  then bool_sort else
    if Types.is_int_type t then int_sort else 
  if Types.is_real_type t then real_sort else 
  match (Types.repr t).Types.tdesc with
  | Types.Tconst ty       -> get_const_sort ty
  | Types.Tclock t        -> type_to_sort t
  | Types.Tarray(dim,ty)   -> Z3.Z3Array.mk_sort !ctx int_sort (type_to_sort ty)
  | Types.Tstatic(d, ty)-> type_to_sort ty
  | Types.Tarrow _
  | _                     -> Format.eprintf "internal error: pp_type %a@."
                               Types.print_ty t; assert false

  
let decl_var id =
  Z3.FuncDecl.mk_func_decl_s !ctx id.var_id [] (type_to_sort id.var_type)

let decl_machine machines m =
  if m.Machine_code.mname.node_id = Machine_code.arrow_id then
    (* We don't print arrow function *)
    ()
  else
    begin
      let _ = List.map decl_var 
      	(
	  (inout_vars machines m)@
	    (rename_current_list (full_memory_vars machines m)) @
	    (rename_mid_list (full_memory_vars machines m)) @
	    (rename_next_list (full_memory_vars machines m)) @
	    (rename_machine_list m.mname.node_id m.mstep.step_locals)
	)
      in
      ()
     (*
      if is_stateless m then
	begin
	  (* Declaring single predicate *)
	  fprintf fmt "(declare-rel %a (%a))@."
	    pp_machine_stateless_name m.mname.node_id
	    (Utils.fprintf_list ~sep:" " pp_type)
	    (List.map (fun v -> v.var_type) (inout_vars machines m));

          match m.mstep.step_asserts with
	  | [] ->
	     begin

	       (* Rule for single predicate *)
	       fprintf fmt "; Stateless step rule @.";
	       fprintf fmt "@[<v 2>(rule (=> @ ";
	       ignore (pp_machine_instrs machines ([] (* No reset info for stateless nodes *) )  m fmt m.mstep.step_instrs);
	       fprintf fmt "@ (%a @[<v 0>%a)@]@]@.))@.@."
		 pp_machine_stateless_name m.mname.node_id
		 (Utils.fprintf_list ~sep:" " (pp_horn_var m)) (inout_vars machines m);
	     end
	  | assertsl ->
	     begin
	       let pp_val = pp_horn_val ~is_lhs:true m.mname.node_id (pp_horn_var m) in
	       
	       fprintf fmt "; Stateless step rule with Assertions @.";
	       (*Rule for step*)
	       fprintf fmt "@[<v 2>(rule (=> @ (and @ ";
	       ignore (pp_machine_instrs machines [] m fmt m.mstep.step_instrs);
	       fprintf fmt "@. %a)@ (%a @[<v 0>%a)@]@]@.))@.@." (pp_conj pp_val) assertsl
		 pp_machine_stateless_name m.mname.node_id
		 (Utils.fprintf_list ~sep:" " (pp_horn_var m)) (step_vars machines m);
	  
	     end
	       
	end
      else
	begin
	  (* Declaring predicate *)
	  fprintf fmt "(declare-rel %a (%a))@."
	    pp_machine_reset_name m.mname.node_id
	    (Utils.fprintf_list ~sep:" " pp_type)
	    (List.map (fun v -> v.var_type) (reset_vars machines m));

	  fprintf fmt "(declare-rel %a (%a))@."
	    pp_machine_step_name m.mname.node_id
	    (Utils.fprintf_list ~sep:" " pp_type)
	    (List.map (fun v -> v.var_type) (step_vars machines m));

	  pp_print_newline fmt ();

	  (* Rule for reset *)
	  fprintf fmt "@[<v 2>(rule (=> @ %a@ (%a @[<v 0>%a)@]@]@.))@.@."
	    (pp_machine_reset machines) m 
	    pp_machine_reset_name m.mname.node_id
	    (Utils.fprintf_list ~sep:"@ " (pp_horn_var m)) (reset_vars machines m);

          match m.mstep.step_asserts with
	  | [] ->
	     begin
	       fprintf fmt "; Step rule @.";
	       (* Rule for step*)
	       fprintf fmt "@[<v 2>(rule (=> @ ";
	       ignore (pp_machine_instrs machines [] m fmt m.mstep.step_instrs);
	       fprintf fmt "@ (%a @[<v 0>%a)@]@]@.))@.@."
		 pp_machine_step_name m.mname.node_id
		 (Utils.fprintf_list ~sep:"@ " (pp_horn_var m)) (step_vars machines m);
	     end
	  | assertsl -> 
	     begin
	       let pp_val = pp_horn_val ~is_lhs:true m.mname.node_id (pp_horn_var m) in
	       (* print_string pp_val; *)
	       fprintf fmt "; Step rule with Assertions @.";
	       
	       (*Rule for step*)
	       fprintf fmt "@[<v 2>(rule (=> @ (and @ ";
	       ignore (pp_machine_instrs machines [] m fmt m.mstep.step_instrs);
	       fprintf fmt "@. %a)@ (%a @[<v 0>%a)@]@]@.))@.@." (pp_conj pp_val) assertsl
		 pp_machine_step_name m.mname.node_id
		 (Utils.fprintf_list ~sep:" " (pp_horn_var m)) (step_vars machines m);
	     end
	       
     	       
	end
      *)  end

           
module Verifier =
  (struct
    include VerifierType.Default
    let name = "zustre"
    let options = []
    let activate () = (
        active := true;
        Options.output := "horn";
      )
    let is_active () = !active

    let get_normalization_params () =
      (* make sure the output is "Horn" *)
      assert(!Options.output = "horn");
      Backends.get_normalization_params ()

    let run basename prog machines =
      let machines = Machine_code.arrow_machine::machines in
      let machines = preprocess machines in
      decl_sorts ();
      List.iter (decl_machine machines) (List.rev machines);

      
      ()

  end: VerifierType.S)
    
