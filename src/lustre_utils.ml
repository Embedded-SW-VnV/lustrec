open Lustre_types

let expr_of_vars loc vl = 
  Corelang.expr_of_expr_list loc
    (List.map Corelang.expr_of_vdecl vl)
   
   
(* Create a node that checks whether two other nodes have the same output *)

let check_eq nd1 nd2 =
  (* TODO: check that nd1 and nd2 have the same signature *)
  let check_nd = Corelang.copy_node nd1 in (* to keep the type info *)
  let loc = Location.dummy_loc in 
  let ok_var =
    Corelang.mkvar_decl loc ~orig:false
      ("__OK",
       Corelang.mktyp loc Tydec_bool,
       Corelang.mkclock loc Ckdec_any,
         false,
       None,
       None)
  in
  let input_e = expr_of_vars loc check_nd.node_inputs in
  let mk_stmt nd out_vars =
    let call_e = Corelang.mkexpr loc (Expr_appl (nd.node_id, input_e , None)) in
    Eq (
        Corelang.mkeq loc
          (List.map (fun v -> v.var_id) out_vars, call_e)) in
  let copy_vars vl post =
    let f v = { (Corelang.copy_var_decl v) with var_id = v.var_id ^ "_" ^ post } in
    List.map f vl
  in
  let out_vars1 = copy_vars nd1.node_outputs "1" in
  let out_vars2 = copy_vars nd1.node_outputs "2" in
  let call_n1 = mk_stmt nd1 out_vars1 in
  let call_n2 = mk_stmt nd2 out_vars2 in
  let build_eq v1 v2 =
    let pair = expr_of_vars loc [v1;v2] in
    Corelang.mkexpr loc (Expr_appl ("=", pair, None))
  in
  let rec build_ok vl1 vl2 =
    match vl1, vl2 with
    | [v1], [v2] -> build_eq v1 v2
    | hd1::tl1, hd2::tl2 -> 
       let e1 = (build_eq hd1 hd2) in
       let e2 = build_ok tl1 tl2 in
       let e = Corelang.mkexpr loc (Expr_tuple [e1; e2]) in
       Corelang.mkexpr loc (Expr_appl ("&&", e, None))
    | _ -> assert false
  in
  let ok_expr  = build_ok out_vars1 out_vars2 in 
  let ok_stmt = Eq (Corelang.mkeq loc ([ok_var.var_id], ok_expr)) in

  (* Building contract *)
    let ok_e = Corelang.expr_of_vdecl ok_var in
  let contract = {
        consts = [];
        locals = [];
       stmts = [];
        assume = [];
        guarantees = [Corelang.mkeexpr loc ok_e];
       modes = [];
        imports = [];
        spec_loc = loc;              
       
      }
  in
  let check_nd = { check_nd with
                   node_id = "check_eq_" ^ nd1.node_id ^ "_" ^ nd2.node_id;
                   node_outputs = [ok_var];
                   node_locals = out_vars1 @ out_vars2;
                   node_stmts = [call_n1; call_n2; ok_stmt];
                   node_spec = Some (Contract contract);
                 }
  in

  
  Global.type_env := Typing.type_node !Global.type_env check_nd loc;
  Global.clock_env := Clock_calculus.clock_node !Global.clock_env loc check_nd;
   
  check_nd
    (*

                   TODO:

                   construire

                   les variables temporaires pour les outputs de l'un et de l'autre
                   les statements d'appels de nodes
                   ok = and (o1 = o2)

                          et on ajoute le contrat guarantee ok
  in
  check_nd 

     *)
    
      (* (\* Build the contract: guarentee output = orig_node(input) *\)
   * 
   * let local_outputs = List.map (fun v -> { (Corelang.copy_var_decl v) with var_id = v.var_id ^ "_local" } ) copy_nd.node_outputs in
   * let input_e = expr_of_vars  copy_nd.node_inputs in
   * let call_orig_e =
   *   Corelang.mkexpr loc (Expr_appl (orig_nd.node_id, input_e , None)) in 
   * let build_orig_outputs =
   *   Eq (
   *       Corelang.mkeq loc
   *         (List.map (fun v -> v.var_id) local_outputs, call_orig_e)) in
   * let eq_expr =  Corelang.expr_of_expr_list loc (
   *                    List.map2 (fun v1 v2 ->
   *                        let args = expr_of_vars [v1;v2] in
   *                          Corelang.mkexpr loc (Expr_appl ("=", args, None)))
   *                  copy_nd.node_outputs local_outputs
   *                  )
   * in
   * let contract = {
   *     consts = [];
   *     locals = local_outputs;
   *     stmts = [build_orig_outputs];
   *     assume = [];
   *     guarantees = [Corelang.mkeexpr loc eq_expr];
   *     modes = [];
   *     imports = [];
   *     spec_loc = loc;              
   *    
   *   }
   * in *)
  
