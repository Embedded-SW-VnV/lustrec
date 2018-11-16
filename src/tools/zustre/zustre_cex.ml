(* Rebuilding Cex *)
(* In order to properly rebuild the Cex, one needsthe unsliced model. Otherwise
   some input or state variables are removed.

*)


open Lustre_types
open Machine_code_types
(* open Machine_code_common *)
open Zustre_common

open Zustre_data

let get_conjuncts e =
  assert (Z3.Boolean.is_bool e);
  if Z3.Boolean.is_and e then
    Z3.Expr.get_args e
  else
    [e]

let build_cex machine machines decl_err =
  (* Recovering associated top machine (to build full traces) and property *) 
  (* TODO: for example extract top node and ok prop. We may have multiple
     MAIN/ERR loaded at the same time. Each of them should be assocaited with a
     CEX/Inv/Timeout.*)
  
  let node_id = machine.mname.node_id in

  let cex = match Z3.Fixedpoint.get_answer !fp with Some e -> e | None -> raise Not_found in
  (* Original code used the function Z3.Fixedpoint.get_ground_sat_answer !fp *)

  let stats = Z3.Fixedpoint.get_statistics !fp in
  
  let conjuncts = List.rev (get_conjuncts cex) in

  Format.eprintf "cex: %s@.%i conjuncts: @[<v 0>%a@]@."
    (Z3.Expr.to_string cex)
    (List.length conjuncts)
    (Utils.fprintf_list ~sep:"@ " (fun fmt e -> Format.fprintf fmt "%s" (Z3.Expr.to_string e))) conjuncts;

  (* Checking size *)
  let inputs = machine.mstep.step_inputs in
  let nb_inputs = List.length inputs in
  let outputs = machine.mstep.step_outputs in
  let nb_outputs = List.length inputs in
  let nb_mems = List.length (full_memory_vars machines machine) in
  
  let main, funs =
    List.fold_left (fun (main, funs) conj ->
    (* Filtering out non MAIN decls *)
    let func_decl = Z3.Expr.get_func_decl conj in
    let node_name = Z3.Symbol.get_string (Z3.FuncDecl.get_name func_decl) in
    (* Focusing only on MAIN_nodeid predicates *)
    if node_name = "MAIN_" ^ node_id then
      (* Extracting info *)
      (* Recall that MAIN args are in@mems@out *)
      let args = Z3.Expr.get_args conj in
      if List.length args = 1 + nb_inputs + nb_mems + nb_outputs then
        (* Should be done with get_int but that function vanished from the opam Z3 API *)
	let id = Big_int.int_of_big_int (Z3.Arithmetic.Integer.get_big_int (List.hd args)) in
	let input_values = Utils.List.extract args 1 (1 + nb_inputs) in
	let output_values = Utils.List.extract args (1+nb_inputs+nb_mems) (1 + nb_inputs + nb_mems + nb_outputs) in
	(id, (input_values, output_values))::main, funs
      else
	assert false
    else
      let reg = Str.regexp_string "[a-z]*_step" in
      if Str.string_match reg node_name 0 then (
	let actual_name = Str.matched_group 0 node_name in
	Format.eprintf "Name %s@." actual_name;
	main, funs
      )
      else (
	Format.eprintf "pas matché %s@." node_name;
	main, funs
      )
    ) ((* main*) [],(* other functions *) []) conjuncts
  in
  let main = List.sort (fun (id1, _) (id2, _) -> compare id1 id2) main in
  List.iter (
    fun (id, expr) ->
      Format.eprintf "Id %i: %a@."
	(id)
	(Utils.fprintf_list ~sep:", "
	   (fun fmt e -> Format.fprintf fmt "%s" (Z3.Expr.to_string e)))
	(fst expr)
  ) main;		    
   (* let ground_val = List.map (fun e -> Z3.Expr.to_string e) (Z3.Expr.get_args conj) in *)

   (* We recover the Zustre XML format, projecting each cex on each input/output
      signal *)
  let in_signals, out_signals =
    List.fold_right (
      fun (id, (sigs_in, sigs_out)) (res_sigs_in, res_sigs_out) ->
	let add l1 l2 = List.map2 (fun e1 e2 -> fst e2, ((id, e1)::(snd e2))) l1 l2 in
	let sigs_in_id = add sigs_in res_sigs_in in
	let sigs_out_id = add sigs_out res_sigs_out in
	sigs_in_id, sigs_out_id
    ) main (List.map (fun v -> v, []) inputs, List.map (fun v -> v, []) outputs)
  in

  (* let _ = List.mapi (fun k conj -> *)
  (*   (\* k-iterate *\) *)
  (*   let ground_val = List.map (fun e -> Z3.Expr.to_string e) (Z3.Expr.get_args conj) in *)
  (*   let func_decl = Z3.Expr.get_func_decl conj in *)
  (*   if !debug then Format.eprintf "FuncDecl %s@." (Z3.FuncDecl.to_string func_decl); *)
  (*   let node_name = Z3.Symbol.get_string (Z3.FuncDecl.get_name func_decl) in *)

   
  (*   if !debug then Format.eprintf "Node %s, args %a@." node_name  (Utils.fprintf_list ~sep:", " (Format.pp_print_string)) ground_val; *)
    
  (*   () *)
  (*   (\*  ground_pair = [] *)
  (*           try: *)
  (*               ground_vars = pred_dict[node_name] *)
  (*               ground_pair = zip(ground_vars,ground_val) *)
  (*               if "_reset" in node_name: *)
  (*                   # this condition is to remove the node nodename_reset added by lustrec *)
  (*                   continue *)
  (*                   # node = node_name.split("_reset")[0] *)
  (*                   # cex_dict.update({node:{k:ground_pair}}) *)
  (*               elif "_step" in node_name: *)
  (*                   node = node_name.split("_step")[0] *)
  (*                   try: *)
  (*                       # case in which we already have the node in dict *)
  (*                       d = cex_dict[node] *)
  (*                       max_key = max(k for k, v in d.iteritems() if v != 0) #get the maximum key value and add 1 *)
  (*                       d.update({(max_key+1):ground_pair}) *)
  (*                   except Exception as e: *)
  (*                       self._log.warning("Adding a new node cex " + str(e)) *)
  (*                       cex_dict.update({node:{k:ground_pair}}) *)
  (*               else: *)
  (*                   node = node_name *)
  (*                   try: *)
  (*                       d = cex_dict[node] *)
  (*                       max_key = max(k for k, v in d.iteritems() if v != 0) #get the maximum key value and add 1 *)
  (*                       d.update({(max_key+1):ground_pair}) *)
  (*                   except Exception as e: *)
  (*                       if node not in ["MAIN", "ERR"]: *)
  (*                           self._log.warning("Adding a new node cex " + str(e)) *)
  (*                           cex_dict.update({node:{k:ground_pair}}) *)
  (*           except Exception as e: *)
  (*               self._log.warning("Problem with getting a node name: " + str(e)) *)
  (*   *\) *)
  (* ) conjuncts in *)
  (*   let rules_expr = Z3.Fixedpoint.get_rules !fp in *)
  (*   if !debug then *)
  (*     Format.eprintf "@[<v 2>Registered rules:@ %a@ @]@." *)
  (* 	(Utils.fprintf_list ~sep:"@ " *)
  (*   	   (fun fmt e -> Format.pp_print_string fmt (Z3.Expr.to_string e)) ) *)
  (* 	rules_expr; *)
  (*   if !debug then *)
  (*     Format.eprintf "FP help: %s@." (Z3.Fixedpoint.get_help !fp); *)

  let stats_entries =   Z3.Statistics.get_entries stats in
  (* List.iter (fun e -> Format.eprintf "%s@.@?" *)
  (*   (Z3.Statistics.Entry.to_string e) *)
    
  (* ) stats_entries; *)
  let json : Yojson.json =
    `Assoc [
      "Results",
      `Assoc [
	"Property",
	`Assoc [
	  "name", `String node_id;
	  "date", `String (Utils.get_date ());
	  "query", `Assoc ["unit", `String "sec";
			   "value", `Float (
			     let time_opt = Z3.Statistics.get stats "time.spacer.solve" in
			     match time_opt with None -> -1.
			     | Some f -> Z3.Statistics.Entry.get_float f)
			  ];
	  "answer", `String "CEX";
	  "counterexample",
	  `Assoc [
	    node_id, `Assoc
	      (
		List.map (fun (vardecl, values) ->
		  vardecl.var_id,
		  `Assoc [
		    "type", (let _ = Format.fprintf Format.str_formatter "%a" Printers.pp_var_type vardecl in
			    let s = Format.flush_str_formatter () in
			    `String s);
		    "values", `Assoc (List.map (fun (id, v) ->
		      string_of_int id, `String (Z3.Expr.to_string v))
					values)
		  ]   
		) in_signals
	      )
	  ]
	]
      ]
     ]
  in
  Format.eprintf "JSON: %s@."
    (Yojson.to_string json);
  ()
  (* Results *)
  (*   Property *)
  (*   Date *)
  (*   Query time *)
  (*   Answer CEX *)
  (*   Counterexample *)
  (*     Node name="nodeid" *)
  (*       Stream name="opt.x" type="unk" *)
  (* 	  Value instant="0">xxx</Value>		       *)
  (* () *)
	(* ordered_by_signal = self.reorder(cex_dict) *)
        (* return self.mk_cex_xml(ordered_by_signal) *)

(* Local Variables: *)
(* compile-command:"make -C ../.. lustrev" *)
(* End: *)

	
