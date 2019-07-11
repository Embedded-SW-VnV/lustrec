(* Multiple export channels for switched systems:
- lustre
- matlab
- text
 *)
open Lustre_types
open Machine_code_types

let verbose = false
            
let to_lustre m sw_init sw_step init_out update_out =
  let orig_nd = m.mname in
  let copy_nd = orig_nd (*Corelang.copy_node orig_nd *) in
  let vl = (* memories *)
    match sw_init with
    | [] -> assert false
    | (gl, up)::_ -> List.map (fun (v,_) -> v) up
  in
(*  let add_pre sw =
    List.map (fun (gl, up) ->
        List.map (fun (g,b) ->
            if not b then
              assert false (* should be guaranted by constrauction *)
            else
              add_pre_expr vl g) gl,
        List.map (fun (v,e) -> add_pre_expr vl e) up
      ) sw
  in
 *)
  
  let rec process_sw f_e sw =
    let process_branch g_opt up =
      let el = List.map (fun (v,e) -> f_e e) up in
      let loc = (List.hd el).expr_loc in
      let new_e = Corelang.mkexpr loc (Expr_tuple el) in
      match g_opt with
        None -> None, new_e, loc
      | Some g ->
         let g = f_e g in
         let ee = Corelang.mkeexpr loc g in
         let new_e = if verbose then
           {new_e with
             expr_annot =
               Some ({annots = [["seal";"guards"],ee];
                      annot_loc = loc})} else new_e 
         in
         Some g, new_e, loc
    in
    match sw with
    | [] -> assert false
    | [g_opt,up] -> ((* last case, no need to guard it *)
      let _, up_e, _ = process_branch g_opt up in
      up_e
    )
    | (g_opt,up)::tl ->
       let g_opt, up_e, loc = process_branch g_opt up in
       match g_opt with
       | None -> assert false (* How could this happen anyway ? *)
       | Some g ->
          let tl_e = process_sw f_e tl in
          Corelang.mkexpr loc (Expr_ite (g, up_e, tl_e)) 
  in
    
  let e_init = process_sw (fun x -> x) sw_init in
  let e_step = process_sw (Corelang.add_pre_expr vl) sw_step in
  let e_init_out = process_sw (fun x -> x) init_out in
  let e_update_out = process_sw (Corelang.add_pre_expr vl) update_out in
  let loc = Location.dummy_loc in
  (* Build the contract: guarentee output = orig_node(input) *)
  let expr_of_vars vl = 
    Corelang.expr_of_expr_list loc
      (List.map Corelang.expr_of_vdecl vl)
  in
  let input_e = expr_of_vars  copy_nd.node_inputs in
  let output_e = expr_of_vars  copy_nd.node_outputs in
  let call_orig_e =
    Corelang.mkexpr loc (Expr_appl (orig_nd.node_id, input_e , None)) in 
  let args = Corelang.mkexpr loc (Expr_tuple([output_e; call_orig_e])) in
  let eq_expr = (Corelang.mkexpr loc (Expr_appl ("=", args, None))) in
  let contract = {
      consts = [];
      locals = [];
      stmts = [];
      assume = [];
      guarantees = [Corelang.mkeexpr loc eq_expr];
      modes = [];
      imports = [];
      spec_loc = loc;              
     
    }
  in
  { copy_nd with
    node_id = copy_nd.node_id ^ "_seal";
    node_locals = m.mmemory;
    node_stmts = [Eq
                    { eq_loc = loc;
                      eq_lhs = vl; 
                      eq_rhs = Corelang.mkexpr loc (Expr_arrow(e_init, e_step))
                    };
                 Eq
                    { eq_loc = loc;
                      eq_lhs = List.map (fun v -> v.var_id) copy_nd.node_outputs; 
                      eq_rhs = Corelang.mkexpr loc (Expr_arrow(e_init_out, e_update_out))
                    };
                 ];
    node_spec = Some (Contract contract);
                 
(*
                   il faut mettre un pre devant chaque memoire dans les updates comme dans les gardes par contre pas besoin de mettre de pre devant les entrees, ni dans les updates, ni dans les gardes


                                                                                                                                                                                        ecrire une expression

                                                                                                                                                                                        (mem1, mem2, mem3) = if garde1 then (e1,e2,e2) else if garde2 then (e1,e2,e3) else ...... else (* garde3 *) (e1,e2,e2)

                                                                                                                                                                                                                                                                                         Il faut aussi calculer la fonction de sortie

  out1,out2 = if garde1 then e1,e2 else if garde2 ....
   *)    
  }
