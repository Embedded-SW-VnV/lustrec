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

let check machines node =

  let machine = get_machine machines node in

  (* Declaring collecting semantics *)
  
  let main_output =
    rename_machine_list machine.mname.node_id machine.mstep.step_outputs
  in
  let main_output_dummy =
    rename_machine_list ("dummy" ^ machine.mname.node_id) machine.mstep.step_outputs
  in
  let main_input = 
    rename_machine_list machine.mname.node_id machine.mstep.step_inputs
  in  
  let main_input_dummy = 
    rename_machine_list ("dummy" ^ machine.mname.node_id) machine.mstep.step_inputs
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
  let decl_main = decl_rel "MAIN" main_memory_next in

  
  
  (* Init case *)
  let decl_init = decl_rel "INIT_STATE" [] in

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
      (List.map horn_var_to_expr main_memory_next)
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
		(List.map horn_var_to_expr vars) 
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
		(List.map horn_var_to_expr (reset_vars machines machine));
	      Z3.Expr.mk_app !ctx
		(get_fdecl (machine_step_name node))
		(List.map horn_var_to_expr (step_vars_m_x machines machine))
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
  
  
  let horn_head = 
    Z3.Expr.mk_app
      !ctx
      decl_main
      (List.map horn_var_to_expr main_memory_next)
  in
  let horn_body =
    Z3.Boolean.mk_and !ctx
      [
	Z3.Expr.mk_app !ctx decl_main (List.map horn_var_to_expr main_memory_current);
	Z3.Expr.mk_app !ctx (get_fdecl (step_name node)) (List.map horn_var_to_expr (step_vars machines machine))
      ]
  in
  (* Vars contains all vars: in_out, current, mid, neXt memories *)
  let vars = (step_vars_c_m_x machines machine) @ main_output_dummy @ main_input_dummy  in
  let _ =
    add_rule ~dont_touch:[decl_main] vars  (Z3.Boolean.mk_implies !ctx horn_body horn_head)
      
  in


  (* Property def *)
  let decl_err = decl_rel "ERR" [] in

  let prop =
    Z3.Boolean.mk_and !ctx (List.map horn_var_to_expr main_output)
  in
  let not_prop =
    Z3.Boolean.mk_not !ctx prop
  in
  add_rule (*~dont_touch:[decl_main;decl_err]*) main_memory_next (Z3.Boolean.mk_implies !ctx
	      (
		Z3.Boolean.mk_and !ctx
		  [not_prop;
		   Z3.Expr.mk_app !ctx decl_main (List.map horn_var_to_expr main_memory_next);
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
  if true then
    Format.eprintf "@[<v 2>Registered rules:@ %a@ @]@."
    (Utils.fprintf_list ~sep:"@ "
       (fun fmt e -> Format.pp_print_string fmt (Z3.Expr.to_string e)) )
    rules_expr;
  let res_status = Z3.Fixedpoint.query_r !fp [decl_err] in

  Format.eprintf "Status: %s@." (Z3.Solver.string_of_status res_status);
  match res_status with
  | Z3.Solver.SATISFIABLE -> (
     (*Zustre_cex.build_cex decl_err*)
    let expr1_opt = Z3.Fixedpoint.get_answer !fp in
    let expr2_opt = Z3.Fixedpoint.get_ground_sat_answer !fp in 
       match expr1_opt, expr2_opt with
	 None, None -> Format.eprintf "Sat No feedback@."
       | Some e, Some e2 -> Format.eprintf "Sat Result: %s, %s@."
					   (Z3.Expr.to_string e)
					   (Z3.Expr.to_string e2)
       | _ -> assert false
  )
  | Z3.Solver.UNSATISFIABLE -> (*build_inv*) (
       let expr_opt = Z3.Fixedpoint.get_answer !fp in
       match expr_opt with
	 None -> Format.eprintf "Unsat No feedback@."
       | Some e -> Format.eprintf "Unsat Result: %s@." (Z3.Expr.to_string e)
  )
  | Z3.Solver.UNKNOWN -> ()
      
(* Local Variables: *)
(* compile-command:"make -C ../.." *)
(* End: *)
