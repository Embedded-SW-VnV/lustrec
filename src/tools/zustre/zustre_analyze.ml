(* This module takes a main node (reset and step) and a property. It assumes
   that the system is properly defined and check that the property is valid. 

   When valid, it returns a set of local invariants. Otherwise, it returns a cex
   expressed as a sequence of input values.

*)
open Lustre_types
open Machine_code_types
open Machine_code_common
open Zustre_common
open Zustre_data

let idx_0 = Z3.Arithmetic.Integer.mk_numeral_i !ctx 0 
let uid_0 = Z3.Z3List.nil uid_sort 
	    
let check machines node =

  let machine = get_machine machines node in
  let node_id = machine.mname.node_id in
  (* Declaring collecting semantics *)
  
  let main_output =
    rename_machine_list node_id machine.mstep.step_outputs
  in
  let main_output_dummy =
    rename_machine_list ("dummy" ^ node_id) machine.mstep.step_outputs
  in
  let main_input = 
    rename_machine_list node_id machine.mstep.step_inputs
  in  
  let main_input_dummy = 
    rename_machine_list ("dummy" ^ node_id) machine.mstep.step_inputs
  in  
  let main_memory_next =
    main_input @ (rename_next_list (* machine.mname.node_id *) (full_memory_vars machines machine)) @
      main_output
  in
  let main_memory_current =
    main_input_dummy @ (rename_current_list (* machine.mname.node_id *) (full_memory_vars machines machine)) @
      main_output_dummy
  in

  (* TODO: push/pop? donner un nom different par instance pour les garder dans le buffer ?
     Faut-il declarer les "rel" dans la hashtbl ?
  *)

  let main_name node_id = "MAIN" ^ "_" ^ node_id in
    
  let decl_main =
    decl_rel ~no_additional_vars:true
      (main_name node_id)
      (int_sort::(List.map (fun v -> type_to_sort v.var_type) (main_memory_next))) in

  
  
  (* Init case *)
  let decl_init = decl_rel ~no_additional_vars:true "INIT_STATE" [] in

  (* (special) rule INIT_STATE *)
  let init_expr = Z3.Expr.mk_app !ctx decl_init [] in
  Z3.Fixedpoint.add_rule !fp init_expr None;
  (* let _ = add_rule [] (Z3.Expr.mk_app *)
  (* 			 !ctx *)
  (* 			 decl_init *)
  (* 			 [] *)
  (* )  in *)

  (* Re-declaring variables *)
  let _ = List.map decl_var main_memory_next in

  let horn_head = 
    Z3.Expr.mk_app
      !ctx
      decl_main
      (idx_0::(* uid_0:: *)(List.map horn_var_to_expr main_memory_next))
  in
  (* Special case when the main node is stateless *)
  let _ =
    if Machine_code_common.is_stateless machine then
      begin
	
	(* Initial set: One Step(m,x)  -- Stateless node  *)	
     	(* rule => (INIT_STATE and step(mid, next)) MAIN(next) *)

	(* Note that vars here contains main_memory_next *)
	let vars = step_vars_m_x machines machine in
	(* Re-declaring variables *)
	let _ = List.map decl_var vars in
	
	let horn_body =
	  Z3.Boolean.mk_and !ctx
	    [
	      Z3.Expr.mk_app !ctx decl_init [];
	      Z3.Expr.mk_app !ctx
		(get_fdecl (machine_stateless_name node))
		(idx_0::uid_0::(List.map horn_var_to_expr vars))
	    ]
	in
	add_rule vars (Z3.Boolean.mk_implies !ctx horn_body horn_head)
	  
	  
      end
    else
      begin
	(* Initial set: Reset(c,m) + One Step(m,x) @. *)

	(* Re-declaring variables *)
	let vars_reset = reset_vars machines machine in
	let vars_step = step_vars_m_x machines machine in
	let vars_step_all = step_vars_c_m_x machines machine in
	let _ = List.map decl_var (vars_reset @ vars_step @ vars_step_all ) in

	(* rule => (INIT_STATE and reset(mid) and step(mid, next)) MAIN(next) *)
	let horn_body =
	  Z3.Boolean.mk_and !ctx
	    [
	      Z3.Expr.mk_app !ctx decl_init [];
	      Z3.Expr.mk_app !ctx
		(get_fdecl (machine_reset_name node))
		(idx_0::uid_0::List.map horn_var_to_expr (reset_vars machines machine));
	      Z3.Expr.mk_app !ctx
		(get_fdecl (machine_step_name node))
		(idx_0::uid_0::List.map horn_var_to_expr (step_vars_m_x machines machine))
	    ]
	in

	(* Vars contains all vars: in_out, current, mid, neXt memories *)
	let vars = step_vars_c_m_x machines machine in
	add_rule vars (Z3.Boolean.mk_implies !ctx horn_body horn_head)
	  
	  
      end
  in
  
  let step_name = 
    if Machine_code_common.is_stateless machine then 
      machine_stateless_name
    else
      machine_step_name
  in
  
  (* ; Inductive def@. *)

  List.iter (fun x -> ignore (decl_var x)) (main_output_dummy @ main_input_dummy);
  
  (* (Utils.fprintf_list ~sep:" " (fun fmt v -> fprintf fmt "%a@." pp_decl_var v)) fmt main_output_dummy; *)

  (* fprintf fmt *)
  (*   "@[<v 2>(rule (=> @ (and @[<v 0>(MAIN %a)@ (@[<v 0>%a %a@])@]@ )@ (MAIN %a)@]@.))@.@." *)
  (*   (Utils.fprintf_list ~sep:" " (pp_horn_var machine)) main_memory_current *)
  (*   step_name node *)
  (*   (Utils.fprintf_list ~sep:" " (pp_horn_var machine)) (step_vars machines machine) *)

  let k = Corelang.dummy_var_decl "k" Type_predef.type_int (*Corelang.mktyp Location.dummy_loc Types.type_int*) in
  let k_var = Z3.Expr.mk_const_f !ctx (decl_var k) in
  
  let horn_head = 
    Z3.Expr.mk_app
      !ctx
      decl_main
      ((Z3.Arithmetic.mk_add
	  !ctx
	  [k_var; Z3.Arithmetic.Integer.mk_numeral_i !ctx 1]
       )::(List.map horn_var_to_expr main_memory_next))
  in
  let horn_body =
    Z3.Boolean.mk_and !ctx
      [
	Z3.Expr.mk_app !ctx decl_main (k_var::(List.map horn_var_to_expr main_memory_current));
	Z3.Expr.mk_app !ctx (get_fdecl (step_name node)) (k_var::uid_0::List.map horn_var_to_expr (step_vars machines machine))
      ]
  in
  (* Vars contains all vars: in_out, current, mid, neXt memories *)
  let vars = (step_vars_c_m_x machines machine) @ main_output_dummy @ main_input_dummy  in
  let _ =
    add_rule ~dont_touch:[decl_main] (k::vars)  (Z3.Boolean.mk_implies !ctx horn_body horn_head)
      
  in


  (* Property def *)
  let decl_err = decl_rel ~no_additional_vars:true "ERR" [] in

  let prop =
    Z3.Boolean.mk_and !ctx (List.map horn_var_to_expr main_output)
  in
  let not_prop =
    Z3.Boolean.mk_not !ctx prop
  in
  add_rule (*~dont_touch:[decl_main;decl_err]*) (k::main_memory_next) (Z3.Boolean.mk_implies !ctx
	      (
		Z3.Boolean.mk_and !ctx
		  [not_prop;
		   Z3.Expr.mk_app !ctx decl_main (k_var::List.map horn_var_to_expr main_memory_next);
		  ]
	      )
	      (Z3.Expr.mk_app !ctx decl_err []))
  ;
  
      (* fprintf fmt "@[<v 2>(rule (=> @ (and @[<v 0>(not %a)@ (MAIN %a)@])@ ERR))@." *)
      (*   (pp_conj (pp_horn_var machine)) main_output *)
      (*   (Utils.fprintf_list ~sep:" " (pp_horn_var machine)) main_memory_next *)
      (*   ; *)
      (*  if !Options.horn_query then fprintf fmt "(query ERR)@." *)

      (* Debug instructions *)
  let rules_expr = Z3.Fixedpoint.get_rules !fp in
  if !debug then
    Format.eprintf "@[<v 2>Registered rules:@ %a@ @]@."
    (Utils.fprintf_list ~sep:"@ "
       (fun fmt e -> Format.pp_print_string fmt (Z3.Expr.to_string e)) )
      rules_expr;
  try
    let res_status = Z3.Fixedpoint.query_r !fp [decl_err] in
    
    Format.eprintf "Status: %s@." (Z3.Solver.string_of_status res_status);
    match res_status with
    | Z3.Solver.SATISFIABLE -> Zustre_cex.build_cex machine machines decl_err
       
    | Z3.Solver.UNSATISFIABLE -> (*build_inv*) (
      let expr_opt = Z3.Fixedpoint.get_answer !fp in
      match expr_opt with
	None -> if !debug then Format.eprintf "Unsat No feedback@."
      | Some e -> if !debug then Format.eprintf "Unsat Result: %s@." (Z3.Expr.to_string e)
    )
    | Z3.Solver.UNKNOWN -> ()
  with Z3.Error msg -> Format.eprintf "Z3 failure: %s@." msg; () 
(* Local Variables: *)
(* compile-command:"make -C ../.. lustrev" *)
(* End: *)
