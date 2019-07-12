open Lustre_types

(* Create a node that checks whether two other nodes have the same output *)

let check_eq nd1 nd2 =
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
  let check_nd = { check_nd with
                   node_id = "check_eq_" ^ nd1.node_id ^ "_" ^ nd2.node_id;
                   node_outputs = [ok_var]; 
                 }
  in
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
   * let expr_of_vars vl = 
   *   Corelang.expr_of_expr_list loc
   *     (List.map Corelang.expr_of_vdecl vl)
   * in
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
  
