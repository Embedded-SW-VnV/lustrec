
(*
TODO

A property/contract is attached to a node foo and could be analyzed
- while considering the exact semantics
- while substituting some callee by their definition (doing it incrementaly ?)
- the returned cex could be given at node level
- or while considering a main node and producing the output at the main node level

One can consider the following algorithm:
- main node foo, local node bar, with a target property/contract
- declare bar using only the contract of its subnodes (callee)
- if the property is valid, 
  - check the validity status of the subnode contracts used
    - if one is not proved, perform the analysis again (of bar contract) using
      the actual definition of the unproven contract
  - return the computed invariants with the dependencies (subcontracts assumed, subcontracts proved)
- if the property is invalid
  - check invalidity wrt to full definition of the node bar (with the actual definition of its subnodes)
  - return the cex
  - try to see if the cex (or a similar violation of the contract) is reachable from its parents 
    (up to main node foo)
    

Other features:
- check equivalence btw two nodes, provided an equivalence map on some callee
  (A equiv B) with map (A id equiv B id) 
  - substitute each callee appearing B nodes 

Analysis:
  - take a main definition, a boolean proposition, and build the collecting semantics
  - then check that the proposition remains valid

*)


open Zustre_common
open Zustre_data

let param_stat = ref false
let param_eldarica = ref false
let param_utvpi = ref false
let param_tosmt = ref false
let param_pp = ref false

let active = ref false

module Verifier =
  (struct
    include VerifierType.Default
    let name = "zustre"
    let options = [
        "-stat", Arg.Set param_stat, "print statistics";
        "-eldarica", Arg.Set param_eldarica, "deactivate fixedpoint extensions when printing rules";
        "-no_utvpi", Arg.Set param_utvpi, "Deactivate UTVPI strategy";
        "-tosmt", Arg.Set param_tosmt, "Print low-level (possibly unreadable) SMT2 statements";
        "-timeout", Arg.Set_int timeout, "Set timeout in ms (default 10000 = 10 s)";
        "-no-pp", Arg.Set param_pp, "No preprocessing (inlining and slicing)";
        "-debug", Arg.Set debug, "Debug mode";
      ]
                
    let activate () = (
        active := true;
        Options.output := "horn";
      )
    let is_active () = !active

    let get_normalization_params () =
      (* make sure the output is "Horn" *)
      assert(!Options.output = "horn");
      Backends.get_normalization_params ()

    let setup_solver () =
      fp := Z3.Fixedpoint.mk_fixedpoint !ctx;
      (* let help = Z3.Fixedpoint.get_help fp in
       * Format.eprintf "Fp help : %s@." help;
       * 
       * let solver =Z3.Solver.mk_solver !ctx None in
       * let help = Z3.Solver.get_help solver in
       * Format.eprintf "Z3 help : %s@." help; *)

      let module P = Z3.Params in
      let module S = Z3.Symbol in
      let mks = S.mk_string !ctx in
      
      (* Fixpoint Engine parameters *)
      
      let fp_params = P.mk_params !ctx in

      (* (\* self.fp.set (engine='spacer') *\) *)
      P.add_symbol fp_params (mks "engine") (mks "spacer");
      (* P.add_symbol fp_params (mks "engine") (mks "pdr");  *)
      
       (* #z3.set_option(rational_to_decimal=True) *)
       (* #self.fp.set('precision',30) *)
      if !param_stat then 
        (* self.fp.set('print_statistics',True) *)
        P.add_bool fp_params (mks "print_statistics") true;

      (* Dont know where to find this parameter *)
      (* if !param_spacer_verbose then
         *   if self.args.spacer_verbose: 
         *        z3.set_option (verbose=1) *)

      (* The option is not recogined*)
      (* self.fp.set('use_heavy_mev',True) *)
      (* P.add_bool fp_params (mks "use_heavy_mev") true; *)
      
      (* self.fp.set('pdr.flexible_trace',True) *)
      P.add_bool fp_params (mks "pdr.flexible_trace") true;

      (* self.fp.set('reset_obligation_queue',False) *)
      P.add_bool fp_params (mks "spacer.reset_obligation_queue") false;

      (* self.fp.set('spacer.elim_aux',False) *)
      P.add_bool fp_params (mks "spacer.elim_aux") false;

      (* if self.args.eldarica:
        *     self.fp.set('print_fixedpoint_extensions', False) *)
      if !param_eldarica then
        P.add_bool fp_params (mks "print_fixedpoint_extensions") false;
      
      (* if self.args.utvpi: self.fp.set('pdr.utvpi', False) *)
      if !param_utvpi then
        P.add_bool fp_params (mks "pdr.utvpi") false;

      (* if self.args.tosmt:
       *        self.log.info("Setting low level printing")
       *        self.fp.set ('print.low_level_smt2',True) *)
      if !param_tosmt then
        P.add_bool fp_params (mks "print.low_level_smt2") true;

      (* if not self.args.pp:
       *        self.log.info("No pre-processing")
       *        self.fp.set ('xform.slice', False)
       *        self.fp.set ('xform.inline_linear',False)
       *        self.fp.set ('xform.inline_eager',False) *\) *)
      if !param_pp then (
        P.add_bool fp_params (mks "xform.slice") false;
        P.add_bool fp_params (mks "xform.inline_linear") false;
        P.add_bool fp_params (mks "xform.inline_eager") false
      );


      (* Ploc's options. Do not seem to have any effect yet *)
      P.add_bool fp_params (mks "print_answer") true;
      P.add_bool fp_params (mks "print_certificate") true;
      P.add_bool fp_params (mks "xform.slice") false;

      (* Adding a timeout *)
      P.add_int fp_params (mks "timeout") !timeout;

      Z3.Fixedpoint.set_parameters !fp fp_params
      
    let run basename prog machines =
      let machines = Machine_code_common.arrow_machine::machines in
      let machines = preprocess machines in
      setup_solver ();


      (* TODO
	 load deps: cf print_dep in horn_backend.ml

      *)
      if false then (
	
	let queries = Z3.Fixedpoint.parse_file !fp "mini.smt2" in

	(* Debug instructions *)
	

	
	let rules_expr = Z3.Fixedpoint.get_rules !fp in
	Format.eprintf "@[<v 2>Registered rules:@ %a@ @]@."
      	  (Utils.fprintf_list ~sep:"@ "
      	     (fun fmt e ->
	       (* let e2 = Z3.Quantifier.get_body eq in *)
	       (* let fd = Z3.Expr.get_func_decl e in *)
	       Format.fprintf fmt "Rule: %s@."
		 (Z3.Expr.to_string e);
	     )) rules_expr;
	
	let _ = List.map extract_expr_fds rules_expr in
	Format.eprintf "%t" pp_fdecls;
	
      	let res_status = Z3.Fixedpoint.query !fp (List.hd queries )in
	
	Format.eprintf "Status: %s@." (Z3.Solver.string_of_status res_status)
      )
      else if false then (

	(* No queries here *)
	let _ = Z3.Fixedpoint.parse_file !fp "mini_decl.smt2" in

	(* Debug instructions *)
	

	
	let rules_expr = Z3.Fixedpoint.get_rules !fp in
	Format.eprintf "@[<v 2>Registered rules:@ %a@ @]@."
      	  (Utils.fprintf_list ~sep:"@ "
      	     (fun fmt e ->
	       (* let e2 = Z3.Quantifier.get_body eq in *)
	       (* let fd = Z3.Expr.get_func_decl e in *)
	       Format.fprintf fmt "Rule: %s@."
		 (Z3.Expr.to_string e);
	     )) rules_expr;
	
	let _ = List.map extract_expr_fds rules_expr in
	Format.eprintf "%t" pp_fdecls;

	if !Options.main_node <> "" then
      	  begin
      	    Zustre_analyze.check machines !Options.main_node

      	  end
	else
      	  failwith "Require main node";

	()	
      )
      else (
	
	
	decl_sorts ();
	
	List.iter (decl_machine machines) (List.rev machines);


	(* (\* Debug instructions *\) *)
	(* let rules_expr = Z3.Fixedpoint.get_rules !fp in *)
	(* Format.eprintf "@[<v 2>Registered rules:@ %a@ @]@." *)
	(* 	(Utils.fprintf_list ~sep:"@ " *)
	(* 	   (fun fmt e -> Format.pp_print_string fmt (Z3.Expr.to_string e)) ) *)
	(* 	rules_expr; *)

	if !Options.main_node <> "" then
      	  begin
      	    Zustre_analyze.check machines !Options.main_node

      	  end
	else
      	  failwith "Require main node";
	
	()
      )
	

	    end: VerifierType.S)
    
(* Local Variables: *)
(* compile-command:"make -C ../.." *)
(* End: *)
