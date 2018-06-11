open Zustre_data

let get_conjuncts e =
  assert (Z3.Boolean.is_bool e);
  if Z3.Boolean.is_and e then
    Z3.Expr.get_args e
  else
    [e]

let build_cex decl_err =

  let cex = match Z3.Fixedpoint.get_answer !fp with Some e -> e | None -> raise Not_found in
       (* Original code used the function Z3.Fixedpoint.get_ground_sat_answer !fp *)
  let conjuncts = List.rev (get_conjuncts cex) in
  (* Predicates are renamed according to the naming scheme of LustreC*)
  (*      pred_dict = {}
        cex_dict = {} #store the cex in order
        for p in self.preds:
            lus_pred = z3.substitute(p, *self.coco.z3MapVar)
            lus_arg = [str(x) for x in lus_pred.children()]
            pred_dict.update({str(lus_pred.decl()):lus_arg})
  *)
  (* Building a cex_dict, a map of maps ! node name -> (k -> value)  *)
  let _ = List.mapi (fun k conj ->
    (* k-iterate *)
    let ground_val = List.map (fun e -> Z3.Expr.to_string e) (Z3.Expr.get_args conj) in
    let func_decl = Z3.Expr.get_func_decl conj in
    if !debug then Format.eprintf "FuncDecl %s@." (Z3.FuncDecl.to_string func_decl);
    let node_name = Z3.Symbol.get_string (Z3.FuncDecl.get_name func_decl) in
    
    if !debug then Format.eprintf "Node %s, args %a@." node_name  (Utils.fprintf_list ~sep:", " (Format.pp_print_string)) ground_val;
    
    ()
    (*  ground_pair = []
            try:
                ground_vars = pred_dict[node_name]
                ground_pair = zip(ground_vars,ground_val)
                if "_reset" in node_name:
                    # this condition is to remove the node nodename_reset added by lustrec
                    continue
                    # node = node_name.split("_reset")[0]
                    # cex_dict.update({node:{k:ground_pair}})
                elif "_step" in node_name:
                    node = node_name.split("_step")[0]
                    try:
                        # case in which we already have the node in dict
                        d = cex_dict[node]
                        max_key = max(k for k, v in d.iteritems() if v != 0) #get the maximum key value and add 1
                        d.update({(max_key+1):ground_pair})
                    except Exception as e:
                        self._log.warning("Adding a new node cex " + str(e))
                        cex_dict.update({node:{k:ground_pair}})
                else:
                    node = node_name
                    try:
                        d = cex_dict[node]
                        max_key = max(k for k, v in d.iteritems() if v != 0) #get the maximum key value and add 1
                        d.update({(max_key+1):ground_pair})
                    except Exception as e:
                        if node not in ["MAIN", "ERR"]:
                            self._log.warning("Adding a new node cex " + str(e))
                            cex_dict.update({node:{k:ground_pair}})
            except Exception as e:
                self._log.warning("Problem with getting a node name: " + str(e))
    *)
  ) conjuncts in
    let rules_expr = Z3.Fixedpoint.get_rules !fp in
    if !debug then
      Format.eprintf "@[<v 2>Registered rules:@ %a@ @]@."
	(Utils.fprintf_list ~sep:"@ "
    	   (fun fmt e -> Format.pp_print_string fmt (Z3.Expr.to_string e)) )
	rules_expr;
    if !debug then
      Format.eprintf "FP help: %s@." (Z3.Fixedpoint.get_help !fp);

  ()
	(* ordered_by_signal = self.reorder(cex_dict) *)
        (* return self.mk_cex_xml(ordered_by_signal) *)


	
