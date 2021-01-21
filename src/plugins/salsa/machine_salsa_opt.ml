(* We try to avoid opening modules here *)
module ST = Salsa.Types
module SDT = SalsaDatatypes
module LT = Lustre_types
module MC = Machine_code

(* Datatype for Salsa: FormalEnv, Ranges, Var set ... *)
open SalsaDatatypes
   
let report = Log.report ~plugin:"salsa" ~verbose_level:Salsa.Log.verbose_level 
(******************************************************************)
(* TODO Xavier: should those functions be declared more globally? *)

let fun_types node = 
  try
    match node.LT.top_decl_desc with 
    | LT.Node nd -> 
      let tin, tout = Types.split_arrow nd.LT.node_type in
      Types.type_list_of_type tin, Types.type_list_of_type tout
    | _ -> Format.eprintf "%a is not a node@.@?" Printers.pp_decl node; assert false
  with Not_found -> Format.eprintf "Unable to find type def for function %s@.@?" (Corelang.node_name node); assert false

let called_node_id m id = 
  let td, _ =
    try
      List.assoc id m.MT.mcalls (* TODO Xavier: mcalls or minstances ? *)
    with Not_found -> assert false
  in
  td
(******************************************************************)    

(* Returns the set of vars that appear in the expression *)
let rec get_expr_real_vars e =
  let open MT in 
  match e.value_desc with
  | Var v  when Types.is_real_type v.LT.var_type -> Vars.singleton v
  | Var _
  | Cst _ -> Vars.empty 
  | Fun (_, args) -> 
    List.fold_left 
      (fun acc e -> Vars.union acc (get_expr_real_vars e)) 
      Vars.empty args
  | Array _
  | Access _
  | Power _ -> assert false 

(* Extract the variables to appear as free variables in expressions (lhs) *)
let rec get_read_vars instrs =
  let open MT in
  match instrs with
    [] -> Vars.empty
  | i::tl -> (
    let vars_tl = get_read_vars tl in 
    match Corelang.get_instr_desc i with
    | MLocalAssign(_,e) 
    | MStateAssign(_,e) -> Vars.union (get_expr_real_vars e) vars_tl
    | MStep(_, _, el) -> List.fold_left (fun accu e -> Vars.union (get_expr_real_vars e) accu) vars_tl el
    | MBranch(e, branches) -> (
      let vars = Vars.union (get_expr_real_vars e) vars_tl in
      List.fold_left (fun vars (_, b) -> Vars.union vars (get_read_vars b) ) vars branches
    )
    | MReset _ 
    | MNoReset _ 
    | MSpec _ | MComment _ -> Vars.empty  
  )

let rec get_written_vars instrs =
  let open MT in
  match instrs with
    [] -> Vars.empty
  | i::tl -> (
    let vars_tl = get_written_vars tl in 
    match Corelang.get_instr_desc i with
    | MLocalAssign(v,_) 
    | MStateAssign(v,_) -> Vars.add v vars_tl 
    | MStep(vdl, _, _) -> List.fold_left (fun accu v -> Vars.add v accu) vars_tl vdl
    | MBranch(_, branches) -> (
      List.fold_left (fun vars (_, b) -> Vars.union vars (get_written_vars b) ) vars_tl branches
    )
    | MReset _ 
    | MNoReset _ 
      | MSpec _ | MComment _ -> Vars.empty    
  )

(* let rec iterTransformExpr fresh_id e_salsa abstractEnv old_range = *)
(*   let new_expr, new_range =  *)
(*     Salsa.MainEPEG.transformExpression fresh_id e_salsa abstractEnv  *)
(*   in *)
(*   Format.eprintf "New range: %a@." 	  RangesInt.pp_val new_range; *)
(*   if Salsa.Float.errLt new_range old_range < 0 then  *)
    
(*     iterTransformExpr fresh_id new_expr abstractEnv new_range *)
(*   else *)
(*     new_expr, new_range *)


(* Takes as input a salsa expression and return an optimized one *)
let opt_num_expr_sliced ranges e_salsa =
  try 
    let fresh_id = "toto"  in (* TODO more meaningful name *)

    let abstractEnv = RangesInt.to_abstract_env ranges in
    report ~level:2 (fun fmt -> Format.fprintf fmt
                                  "Launching analysis: %s@ "
                                  (Salsa.Print.printExpression e_salsa));
    let new_e_salsa, e_val = 
      Salsa.MainEPEG.transformExpression fresh_id e_salsa abstractEnv
    in
    report ~level:2 (fun fmt -> Format.fprintf fmt " Analysis done: %s@ "
      (Salsa.Print.printExpression new_e_salsa));


    (* (\* Debug *\) *)
    (* Format.eprintf "Salsa:@.input expr: %s@.outputexpr: %s@." *)
    (*   (Salsa.Print.printExpression e_salsa) *)
    (*   (Salsa.Print.printExpression new_e_salsa); *)
    (* (\* Debug *\) *)
    
    report ~level:2 (fun fmt -> Format.fprintf fmt " Computing range progress@ ");

    let old_val = Salsa.Analyzer.evalExpr e_salsa abstractEnv [] in
    let expr, expr_range  =
      match RangesInt.Value.leq old_val e_val, RangesInt.Value.leq e_val old_val with
      | true, true -> (
	if !debug then report ~level:2 (fun fmt ->
	  Format.fprintf fmt "No improvement on abstract value %a@ " RangesInt.pp_val e_val;
	);
	e_salsa, Some old_val
      )
      | false, true -> (
	if !debug then report ~level:2 (fun fmt ->
	  Format.fprintf fmt "Improved!@ ";
	);
	new_e_salsa, Some e_val
      )
      | true, false ->
         report ~level:2 (fun fmt ->
             Format.fprintf fmt
               "CAREFUL --- new range is worse!. Restoring provided expression@ ");
 	     e_salsa, Some old_val

      | false, false -> (
        report ~level:2 (fun fmt ->
            Format.fprintf fmt
	      "Error; new range is not comparable with old end. It may need some investigation!@. ";
	    Format.fprintf fmt "old: %a@.new: %a@ "
	      RangesInt.pp_val old_val
	      RangesInt.pp_val e_val);
	
	new_e_salsa, Some e_val
       	(* assert false *)
      )
    in
    report ~level:2 (fun fmt -> Format.fprintf fmt " Computing range done@ ");

    if !debug then report ~level:2 (fun fmt ->
      Format.fprintf fmt
	"  @[<v>old_expr: @[<v 0>%s@ range: %a@]@ new_expr: @[<v 0>%s@ range: %a@]@ @]@ "
	(Salsa.Print.printExpression e_salsa)
	(* MC.pp_val e *)
	RangesInt.pp_val old_val
	(Salsa.Print.printExpression new_e_salsa)
	(* MC.pp_val new_e *)
	RangesInt.pp_val e_val;
    );
    expr, expr_range
  with (* Not_found ->  *)
  | Salsa.Epeg_types.EPEGError _ -> (
    report ~level:2 (fun fmt ->
      Format.fprintf fmt
	"BECAUSE OF AN ERROR, Expression %s was not optimized@ " 	(Salsa.Print.printExpression e_salsa)
(* MC.pp_val e *));
    e_salsa, None
  )


     
(* Optimize a given expression. It returns the modified expression, a computed range and freshly defined variables. *)
let optimize_expr nodename m constEnv printed_vars vars_env ranges formalEnv e : MT.value_t * RangesInt.t option * MT.instr_t list * Vars.VarSet.t = 
  let rec opt_expr m vars_env ranges formalEnv e =
    let open MT in
    match e.value_desc with
    | Cst cst ->
       (* Format.eprintf "optmizing constant expr @ "; *)
       (* the expression is a constant, we optimize it directly if it is a real
  	  constant *)
       let typ = Typing.type_const Location.dummy_loc cst in
       if Types.is_real_type typ then 
	 opt_num_expr m vars_env ranges formalEnv e 
       else e, None, [], Vars.empty
    | Var v -> 
       if not (Vars.mem v printed_vars) && 
	    (* TODO xavier: comment recuperer le type de l'expression? Parfois e.value_type vaut 'd *)
	    (Types.is_real_type e.value_type ||  Types.is_real_type v.LT.var_type) 
       then
	 opt_num_expr m vars_env ranges formalEnv e 
       else 
	 e, None, [],  Vars.empty  (* Nothing to optimize for expressions containing a single non real variable *)
    (* (\* optimize only numerical vars *\) *)
    (* if Type_predef.is_real_type v.LT.var_type then opt_num_expr ranges formalEnv e *)
    (* else e, None *)
    | Fun (fun_id, args) -> (
      (* necessarily, this is a basic function (ie. + - * / && || mod ... ) *)
      (* if the return type is real then optimize it, otherwise call recusrsively on arguments *)
      if Types.is_real_type e.value_type then
	opt_num_expr m vars_env ranges formalEnv e 
      else (
	(* We do not care for computed local ranges. *)
  	let args', il, new_locals =
	  List.fold_right (
	      fun arg (al, il, nl) ->
	      let arg', _, arg_il, arg_nl =
		opt_expr m vars_env ranges formalEnv arg in
	      arg'::al, arg_il@il, Vars.union arg_nl nl)
	    args
	    ([], [], Vars.empty)
	in
  	{ e with value_desc = Fun(fun_id, args')}, None, il, new_locals	  
      )
    )
    | Array _
      | Access _
      | Power _ -> assert false  
  and opt_num_expr m vars_env ranges formalEnv e = 
    if !debug then (
      report ~level:2 (fun fmt -> Format.fprintf fmt "Optimizing expression @[<hov>%a@]@ "
	                            (MC.pp_val m) e);
    );
    (* if !debug then Format.eprintf "Optimizing expression %a with Salsa@ " MC.pp_val e;  *)
    (* Convert expression *)
    (* List.iter (fun (l,c) -> Format.eprintf "%s -> %a@ " l Printers.pp_const c) constEnv; *)
    let e_salsa : Salsa.Types.expression = value_t2salsa_expr constEnv e in
    (* Format.eprintf "apres deplaige constantes ok%a @." MC.pp_val (salsa_expr2value_t vars_env [](\* constEnv *\) e_salsa) ;  *)

    (* Convert formalEnv *)
    (* if !debug then Format.eprintf "Formal env is [%a]@ " FormalEnv.pp formalEnv; *)
    (* if !debug then Format.eprintf "Formal env converted to salsa@ "; *)

    (* Format.eprintf "Expression avant et apres substVars.@.Avant %a@." MC.pp_val (salsa_expr2value_t vars_env [] e_salsa) ;   *)

    (* Substitute all occurences of variables by their definition in env *)
    let (e_salsa: Salsa.Types.expression), _ = 
      Salsa.Rewrite.substVars 
	e_salsa
	(FormalEnv.to_salsa constEnv formalEnv)
	0 (* TODO: Nasrine, what is this integer value for ? *)
    in

    (* Format.eprintf "Apres %a@." MC.pp_val (salsa_expr2value_t vars_env [] e_salsa) ;   *)

    (* if !debug then Format.eprintf "Substituted def in expr@ "; *)
    let abstractEnv = RangesInt.to_abstract_env ranges in
    (* List.iter (fun (id, _) -> Format.eprintf "absenv: %s@." id) abstractEnv; *)
    (* The expression is partially evaluated by the available ranges
       valEnv2ExprEnv remplce les paires id, abstractVal par id, Cst itv - on
       garde evalPartExpr remplace les variables e qui sont dans env par la cst
       - on garde *)
    (* if !debug then Format.eprintf "avant avant eval part@ "; *)
    (* Format.eprintf "avant evalpart: %a@." MC.pp_val (salsa_expr2value_t vars_env constEnv e_salsa); *)
    let e_salsa =  
      Salsa.Analyzer.evalPartExpr 
	e_salsa
	(Salsa.Analyzer.valEnv2ExprEnv abstractEnv) 
	([] (* no blacklisted variables *))
	([] (* no arrays *))
    in
    (* Format.eprintf "apres evalpart: %a@." MC.pp_val (salsa_expr2value_t vars_env constEnv e_salsa); *)
    (* Checking if we have all necessary information *)

    let free_vars = get_salsa_free_vars vars_env constEnv abstractEnv e_salsa in
    if Vars.cardinal free_vars > 0 then (
      report ~level:2 (fun fmt -> Format.fprintf fmt
	                                "Warning: unbounded free vars (%a) in expression %a. We do not optimize it.@ " 
	                                Vars.pp (Vars.fold (fun v accu ->
	                                             let v' = {v with LT.var_id = nodename.LT.node_id ^ "." ^ v.LT.var_id } in
	                                             Vars.add v' accu)
		                                   free_vars Vars.empty)
	                                (MC.pp_val m) (salsa_expr2value_t vars_env constEnv e_salsa));
      if !debug then report ~level:2 (fun fmt -> Format.fprintf fmt  "Some free vars, not optimizing@ ");
      if !debug then report ~level:3 (fun fmt -> Format.fprintf fmt "  ranges: %a@ "
	                                               RangesInt.pp ranges);

      (* if !debug then Log.report ~level:2 (fun fmt -> Format.fprintf fmt "Formal env was @[<v 0>%a@]@ " FormalEnv.pp formalEnv); *)
      
      
      let new_e = try salsa_expr2value_t vars_env constEnv e_salsa   with Not_found -> assert false in
      new_e, None, [] , Vars.empty
    )
    else (
      
      if !debug then
	report ~level:3 (fun fmt -> Format.fprintf fmt "@[<v 2>Analyzing expression %a@  with ranges: @[<v>%a@ @]@ @]@ "
	                                  (C_backend_common.pp_c_val m "" (C_backend_common.pp_c_var_read m)) (salsa_expr2value_t vars_env constEnv e_salsa)
	                                  (Utils.fprintf_list ~sep:",@ "(fun fmt (l,r) -> Format.fprintf fmt "%s -> %a" l FloatIntSalsa.pp r)) abstractEnv)
      
      ;

        (* Slicing expression *)
        let e_salsa, seq =
	  try
	    Salsa.Rewrite.sliceExpr e_salsa 0 (Salsa.Types.Nop(Salsa.Types.Lab 0))
	  with _ -> Format.eprintf "Issues rewriting express %s@.@?" (Salsa.Print.printExpression e_salsa); assert false
        in
        let def_tmps = Salsa.Utils.flatten_seq seq [] in
        (* Registering tmp ids in vars_env *)
        let vars_env', new_local_vars = List.fold_left
	                                  (fun (vs,vars) (id, _) ->
	                                    let vdecl = Corelang.mk_fresh_var
	                                                  (nodename.node_id, []) (* TODO check that the empty env is ok. One may need to build or access to the current env *)
	                                                  Location.dummy_loc
	                                                  e.MT.value_type
	                                                  (Clocks.new_var true)
	                                              
	                                    in
	                                    let vs' =
	                                      VarEnv.add
	                                        id
	                                        {
		                                  vdecl = vdecl ;
		                                  is_local = true;
	                                        }
	                                        vs
	                                    in
	                                    let vars' = Vars.add vdecl vars in
	                                    vs', vars'
	                                  )
	                                  (vars_env,Vars.empty)
	                                  def_tmps
        in 
        (* Debug *)
        if !debug then (
	  report ~level:3 (fun fmt ->
	      Format.fprintf  fmt "List of slices: @[<v 0>%a@]@ "
	        (Utils.fprintf_list
	           ~sep:"@ "
	           (fun fmt (id, e_id) ->
		     Format.fprintf fmt "(%s,%a) -> %a"
		       id
		       Printers.pp_var (get_var vars_env' id).vdecl
		       (C_backend_common.pp_c_val m "" (C_backend_common.pp_c_var_read m)) (salsa_expr2value_t vars_env' constEnv e_id)
	           )
	        )
	        def_tmps;
	      Format.fprintf fmt "Sliced expression: %a@ "
	        (C_backend_common.pp_c_val m "" (C_backend_common.pp_c_var_read m)) (salsa_expr2value_t vars_env' constEnv e_salsa)
	      ;
	));
        (* Debug *)
        
        (* Optimize def tmp, and build the associated instructions.  Update the
	 abstract Env with computed ranges *)
        if !debug && List.length def_tmps >= 1 then (
	  report ~level:3 (fun fmt -> Format.fprintf fmt "@[<v 3>Optimizing sliced sub-expressions@ ")
        );
        let rev_def_tmp_instrs, ranges =
	  List.fold_left (fun (accu_instrs, ranges) (id, e_id) ->
	      (* Format.eprintf "Cleaning/Optimizing %s@." id; *)
	      let e_id', e_range = (*Salsa.MainEPEG.transformExpression id e_id abstractEnv*)
	        opt_num_expr_sliced ranges e_id
	      in
	      let new_e_id' = try salsa_expr2value_t vars_env' constEnv e_id'  with Not_found -> assert false in

	      let vdecl = (get_var vars_env' id).vdecl in
	      
	      let new_local_assign =
	        (* let expr = salsa_expr2value_t vars_env' constEnv e_id' in *)
	        MT.MLocalAssign(vdecl, new_e_id')
	      in
	      let new_local_assign = {
	          MT.instr_desc = new_local_assign;
	          MT.lustre_eq = None (* could be Corelang.mkeq Location.dummy_loc
				   ([vdecl.LT.var_id], e_id) provided it is
				   converted as Lustre expression rather than
				   a Machine code value *);
	        }
	      in
	      let new_ranges =
	        match e_range with
	          None -> ranges
	        | Some e_range -> RangesInt.add_def ranges id e_range in
	      new_local_assign::accu_instrs, new_ranges
	    ) ([], ranges) def_tmps
        in
        if !debug && List.length def_tmps >= 1 then (
	  report ~level:3 (fun fmt -> Format.fprintf fmt "@]@ ")
        );

        (* Format.eprintf "Optimizing main expression %s@.AbstractEnv is %a" (Salsa.Print.printExpression e_salsa) RangesInt.pp ranges; *)
        

        let expr_salsa, expr_range = opt_num_expr_sliced ranges e_salsa in
        let expr = try salsa_expr2value_t vars_env' constEnv expr_salsa   with Not_found -> assert false in

        expr, expr_range, List.rev rev_def_tmp_instrs, new_local_vars



    (* ???? Bout de code dans unstable lors du merge avec salsa ? 
      ====

      let new_e = try salsa_expr2value_t vars_env' constEnv new_e_salsa   with Not_found -> assert false in
	if !debug then Log.report ~level:2 (fun fmt ->
	  let old_range = Salsa.Analyzer.evalExpr e_salsa abstractEnv [] in
	  match RangesInt.Value.leq old_range e_val, RangesInt.Value.leq e_val old_range with
	  | true, true -> Format.fprintf fmt "No improvement on abstract value %a@ " RangesInt.pp_val e_val
	  | true, false -> (
	    Format.fprintf fmt "Improved!";
	    Format.fprintf fmt
	      "  @[<v>old_expr: @[<v 0>%a@ range: %a@]@ new_expr: @[<v 0>%a@ range: %a@]@ @]@ "
	      (MC.pp_val m) e
	      RangesInt.pp_val (Salsa.Analyzer.evalExpr e_salsa abstractEnv [])
	      (MC.pp_val m) new_e
	      RangesInt.pp_val e_val
	  )
	  | false, true -> Format.eprintf "Error; new range is worse!@.@?"; assert false
	  | false, false -> Format.eprintf "Error; new range is not comparabe with old end. This should not happen!@.@?"; assert false
	);
	new_e, Some e_val, List.rev rev_def_tmp_instrs
      with (* Not_found ->  *)
      | Salsa.Epeg_types.EPEGError _ -> (
	Log.report ~level:2 (fun fmt -> Format.fprintf fmt "BECAUSE OF AN ERROR, Expression %a was not optimized@ " (MC.pp_val m) e);
	e, None, []
      )
>>>>>>> unstable
     *)
    )


    
  in
  opt_expr m vars_env ranges formalEnv e  
    
    
(* Returns a list of assign, for each var in vars_to_print, that produce the
   definition of it according to formalEnv, and driven by the ranges. *)
let assign_vars nodename m constEnv vars_env printed_vars ranges formalEnv vars_to_print =
  (* We print thhe expression in the order of definition *)

  let ordered_vars = 
    List.stable_sort
      (FormalEnv.get_sort_fun formalEnv) 
      (Vars.elements vars_to_print) 
  in
  if !debug then report ~level:4 (fun fmt -> Format.fprintf fmt
    "Printing vars in the following order: [%a]@ "
    (Utils.fprintf_list ~sep:", " Printers.pp_var) ordered_vars);
  
  List.fold_right (
    fun v (accu_instr, accu_ranges, accu_new_locals) -> 
      if !debug then report ~level:4 (fun fmt -> Format.fprintf fmt "Printing assign for variable %s@ " v.LT.var_id);
      try
	(* Obtaining unfold expression of v in formalEnv *)
	let v_def = FormalEnv.get_def formalEnv v  in
	let e, r, il, new_v_locals =
	  optimize_expr nodename m constEnv printed_vars vars_env ranges formalEnv v_def
	in
	let instr_desc = 
	  if try (get_var vars_env v.LT.var_id).is_local with Not_found -> assert false then
	    MT.MLocalAssign(v, e)
	  else
	    MT.MStateAssign(v, e)
	in
	  (il@((Corelang.mkinstr instr_desc)::accu_instr)), 
	    (
	      match r with 
	      | None -> ranges 
	      | Some v_r -> RangesInt.add_def ranges v.LT.var_id v_r),
	    (Vars.union accu_new_locals new_v_locals)
      with FormalEnv.NoDefinition _ -> (
	(* It should not happen with C backend, but may happen with Lustre backend *)
	if !Options.output = "lustre" then accu_instr, ranges, Vars.empty else (Format.eprintf "@?"; assert false)
      )
  ) ordered_vars ([], ranges, Vars.empty)

(* Main recursive function: modify the instructions list while preserving the
   order of assigns for state variables. Returns a quintuple: (new_instrs,
   ranges, formalEnv, printed_vars, and remaining vars to be printed) *)
let rec rewrite_instrs nodename m constEnv  vars_env m instrs ranges formalEnv printed_vars vars_to_print =
  let formal_env_def = FormalEnv.def constEnv vars_env in
  (* Format.eprintf "Rewrite intrs : [%a]@." MC.pp_instrs instrs; *)
  let assign_vars = assign_vars nodename m constEnv vars_env in
  (* if !debug then ( *)
  (*   Log.report ~level:3 (fun fmt -> Format.fprintf fmt    *)
  (*     "Current printed_vars: [%a]@ Vars to print: [%a]@ Formal env is [%a]@ " *)
  (*     Vars.pp printed_vars *)
  (*     Vars.pp vars_to_print *)
  (*     FormalEnv.pp formalEnv) *)
  (* ); *)
  match instrs with
  | [] -> 
     (* End of instruction list: we produce the definition of each variable that
	appears in vars_to_print. Each of them should be defined in formalEnv *)
     (* if !debug then Format.eprintf "Producing definitions %a@ " Vars.pp vars_to_print; *)
    let instrs, ranges', new_expr_locals = assign_vars printed_vars ranges formalEnv vars_to_print in
    instrs,
    ranges',     
    formalEnv,
    Vars.union printed_vars vars_to_print, (* We should have printed all required vars *)
    [], (* No more vars to be printed *)
    Vars.empty
      
  | hd_instr::tl_instrs -> 
     (* We reformulate hd_instr, producing or not a fresh instruction, updating
	formalEnv, possibly ranges and vars_to_print *)
     begin
       let hd_instrs, ranges, formalEnv, printed_vars, vars_to_print, hd_new_locals =
	 match Corelang.get_instr_desc hd_instr with 
	 | MT.MLocalAssign(vd,vt) when Types.is_real_type vd.LT.var_type  && not (Vars.mem vd vars_to_print) -> 
	   (* LocalAssign are injected into formalEnv *)
	   (* if !debug then Format.eprintf "Registering local assign %a@ " MC.pp_instr hd_instr; *)
	   (* if !debug then Format.eprintf "%a@ " MC.pp_instr hd_instr; *)
	   let formalEnv' = formal_env_def formalEnv vd vt in (* formelEnv updated with vd = vt *)
	   [],                        (* no instr generated *)
	   ranges,                    (* no new range computed *)
	   formalEnv',
	   printed_vars,              (* no new printed vars *)
	   vars_to_print,              (* no more or less variables to print *)
	   Vars.empty              (* no new locals *)
	   
	 | MT.MLocalAssign(vd,vt) when Types.is_real_type vd.LT.var_type && Vars.mem vd vars_to_print ->

           (* if !debug then Format.eprintf "Registering and producing state assign %a@ " MC.pp_instr hd_instr; *)
           (* if !debug then Format.eprintf "Registering and producing state assign %a@ " MC.pp_instr hd_instr; *)
           (* if !debug then ( *)
	   (*   Format.eprintf "%a@ " MC.pp_instr hd_instr; *)
	   (*   Format.eprintf "Selected var %a: producing expression@ " Printers.pp_var vd; *)
	   (* ); *)
	   let formalEnv' = formal_env_def formalEnv vd vt in (* formelEnv updated with vd = vt *)
	   let instrs', ranges', expr_new_locals = (* printing vd = optimized vt *)
	     assign_vars printed_vars ranges formalEnv' (Vars.singleton vd)  
	   in
	   instrs',
	   ranges',                          (* no new range computed *)
	   formalEnv',                       (* formelEnv already updated *)
	   Vars.add vd printed_vars,         (* adding vd to new printed vars *)
	   Vars.remove vd vars_to_print,     (* removed vd from variables to print *)
	   expr_new_locals                   (* adding sliced vardecl to the list *)
	     
	 | MT.MStateAssign(vd,vt) when Types.is_real_type vd.LT.var_type (* && Vars.mem vd vars_to_print  *)-> 

	   (* StateAssign are produced since they are required by the function. We still
	      keep their definition in the formalEnv in case it can optimize later
	      outputs. vd is removed from remaining vars_to_print *)
	   (* if !debug then Format.eprintf "Registering and producing state assign %a@ " MC.pp_instr hd_instr; *)
           (* if !debug then ( *)
	   (*   Format.eprintf "%a@ " MC.pp_instr hd_instr; *)
	   (*   Format.eprintf "State assign %a: producing expression@ " Printers.pp_var vd; *)
	   (* ); *)
	   let formalEnv' = formal_env_def formalEnv vd vt in (* formelEnv updated with vd = vt *) 
	   let instrs', ranges', expr_new_locals = (* printing vd = optimized vt *)
	     assign_vars printed_vars ranges formalEnv' (Vars.singleton vd)  
	   in
	   instrs',
	   ranges',                          (* no new range computed *)
	   formalEnv,                        (* formelEnv already updated *)
	   Vars.add vd printed_vars,         (* adding vd to new printed vars *)
	   Vars.remove vd vars_to_print,     (* removed vd from variables to print *)
	   expr_new_locals                   (* adding sliced vardecl to the list *)

	 | (MT.MLocalAssign(vd,vt) | MT.MStateAssign(vd,vt))  ->
	    (* Format.eprintf "other assign %a@." MC.pp_instr hd_instr; *)

	   (* We have to produce the instruction. But we may have to produce as
	      well its dependencies *)
	   let required_vars = get_expr_real_vars vt in
	   let required_vars = Vars.diff required_vars printed_vars in (* remove
									  already
									  produced
									  variables *)
	   (* Format.eprintf "Required vars: %a@." Vars.pp required_vars; *)
	   let required_vars = Vars.diff required_vars (Vars.of_list m.MT.mmemory) in
	   let prefix_instr, ranges, new_expr_dep_locals  = 
	     assign_vars printed_vars ranges formalEnv required_vars in

	   let vt', _, il, expr_new_locals = optimize_expr nodename m constEnv (Vars.union required_vars printed_vars) vars_env ranges formalEnv vt in
	   let new_instr = 
	     match Corelang.get_instr_desc hd_instr with
	     | MT.MLocalAssign _ -> Corelang.update_instr_desc hd_instr (MT.MLocalAssign(vd,vt'))
	     | _ -> Corelang.update_instr_desc hd_instr (MT.MStateAssign(vd,vt'))
	   in
	   let written_vars = Vars.add vd required_vars in
	   prefix_instr@il@[new_instr],
	   ranges,                          (* no new range computed *)
	   formalEnv,                       (* formelEnv untouched *)
	   Vars.union written_vars printed_vars,  (* adding vd + dependencies to
						     new printed vars *)
	   Vars.diff vars_to_print written_vars, (* removed vd + dependencies from
						   variables to print *)
	   (Vars.union new_expr_dep_locals expr_new_locals)
	 | MT.MStep(vdl,id,vtl) ->
	    (* Format.eprintf "step@."; *)

	   (* if !debug then Format.eprintf "Call to a node %a@ " MC.pp_instr hd_instr; *)
	   (* Call of an external function. Input expressions have to be
	      optimized, their free variables produced. A fresh range has to be
	      computed for each output variable in vdl. Output of the function
	      call are removed from vars to be printed *)
	   let node =  called_node_id m id in
	   let node_id = Corelang.node_name node in
	   let tin, tout =  (* special care for arrow *)
	     if node_id = "_arrow" then
	       match vdl with 
	       | [v] -> let t = v.LT.var_type in
			[t; t], [t]
	       | _ -> assert false (* should not happen *)
	     else
	       fun_types node
	   in
	   (* if !debug then Format.eprintf "@[<v 2>... optimizing arguments@ "; *)
	   let vtl', vtl_ranges, il, args_new_locals = List.fold_right2 (
	     fun e typ_e (exprl, range_l, il_l, new_locals)-> 
	       if Types.is_real_type typ_e then
		 let e', r', il, new_expr_locals =
		   optimize_expr nodename m constEnv printed_vars vars_env ranges formalEnv e
		 in
		 e'::exprl, r'::range_l, il@il_l, Vars.union new_locals new_expr_locals
	       else 
		 e::exprl, None::range_l, il_l, new_locals
	   ) vtl tin ([], [], [], Vars.empty) 
	   in 
	   (* if !debug then Format.eprintf "... done@ @]@ "; *)



	   (* let required_vars =  *)
	   (*   List.fold_left2  *)
	   (*     (fun accu e typ_e ->  *)
	   (* 	 if Types.is_real_type typ_e then *)
	   (* 	   Vars.union accu (get_expr_real_vars e)  *)
	   (* 	 else (\* we do not consider non real expressions *\) *)
	   (* 	   accu *)
	   (*     ) *)
 	   (*     Vars.empty  *)
	   (*     vtl' tin *)
	   (* in *)
	   (* if !debug then Format.eprintf "Required vars: [%a]@ Printed vars: [%a]@ Remaining required vars: [%a]@ " *)
	   (*   Vars.pp required_vars  *)
	   (*   Vars.pp printed_vars *)
	   (*   Vars.pp (Vars.diff required_vars printed_vars) *)
	   (* ; *)
	   (* let required_vars = Vars.diff required_vars printed_vars in (\* remove *)
	   (* 								  already *)
	   (* 								  produced *)
	   (* 								  variables *\) *)
	   (* let written_vars = Vars.union required_vars (Vars.of_list vdl) in *)
	   (* let instrs', ranges' = assign_vars (Vars.union written_vars printed_vars) ranges formalEnv required_vars in *)

	   (* instrs' @ [Corelang.update_instr_desc hd_instr (MT.MStep(vdl,id,vtl'))], (* New instrs *) *)

	   let written_vars = Vars.of_list vdl in
	   

	   
	   il @ [Corelang.update_instr_desc hd_instr (MT.MStep(vdl,id,vtl'))], (* New instrs *)
	   RangesInt.add_call ranges vdl id vtl_ranges,   (* add information bounding each vdl var *) 
	   formalEnv,
	   Vars.union written_vars printed_vars,        (* adding vdl to new printed vars *)
	   Vars.diff vars_to_print written_vars,
	   args_new_locals
	     
	 | MT.MBranch(vt, branches) ->
	    
	    (* Required variables to compute vt are introduced. 
	       Then each branch is refactored specifically 
	    *)
	    
	    (* if !debug then Format.eprintf "Branching %a@ " MC.pp_instr hd_instr; *)
	    let required_vars = get_expr_real_vars vt in
	    let required_vars = Vars.diff required_vars printed_vars in (* remove
									   already
									   produced
									   variables *)
	    let vt', _, prefix_instr, prefix_new_locals = optimize_expr nodename m constEnv printed_vars vars_env ranges formalEnv vt in

	    let new_locals = prefix_new_locals in
	    
	   (* let prefix_instr, ranges =  *)
	   (*   assign_vars (Vars.union required_vars printed_vars) ranges formalEnv required_vars in *)

	   let printed_vars = Vars.union printed_vars required_vars in


	   let read_vars_tl = get_read_vars tl_instrs in
	   (* if !debug then Format.eprintf "@[<v 2>Dealing with branches@ "; *)
	   let branches', written_vars, merged_ranges, new_locals = List.fold_right (
	     fun (b_l, b_instrs) (new_branches, written_vars, merged_ranges, new_locals) -> 
	       let b_write_vars = get_written_vars b_instrs in
	       let b_vars_to_print = Vars.inter b_write_vars (Vars.union read_vars_tl vars_to_print) in 
	       let b_fe = formalEnv in               (* because of side effect
							data, we copy it for
							each branch *)
	       let b_instrs', b_ranges, b_formalEnv, b_printed, b_vars, b_new_locals = 
		 rewrite_instrs nodename m constEnv  vars_env m b_instrs ranges b_fe printed_vars b_vars_to_print 
	       in
	       (* b_vars should be empty *)
	       let _ = if b_vars != [] then assert false in
	       
	       (* Producing the refactored branch *)
	       (b_l, b_instrs') :: new_branches,
	       Vars.union b_printed written_vars, (* They should coincides. We
						     use union instead of
						     inter to ease the
						     bootstrap *)
	       RangesInt.merge merged_ranges b_ranges,
	       Vars.union new_locals b_new_locals
		 
	   ) branches ([], required_vars, ranges, new_locals)
	   in
	   (* if !debug then Format.eprintf "dealing with branches done@ @]@ ";	   *)
	   prefix_instr@[Corelang.update_instr_desc hd_instr (MT.MBranch(vt', branches'))],
	   merged_ranges, (* Only step functions call within branches may have
			     produced new ranges. We merge this data by
			     computing the join per variable *)
	   formalEnv,    (* Thanks to the computation of var_to_print in each
			    branch, no new definition should have been computed
			    without being already printed *)
	   Vars.union written_vars printed_vars,
	   Vars.diff vars_to_print written_vars (* We remove vars that have been
						   produced within branches *),
	   new_locals


	 | MT.MReset(_) | MT.MNoReset _ | MT.MSpec _ | MT.MComment _ ->
	    (* if !debug then Format.eprintf "Untouched %a (non real)@ " MC.pp_instr hd_instr; *)

	   (* Untouched instruction *)
	   [ hd_instr ],                    (* unmodified instr *)
	   ranges,                          (* no new range computed *)
	   formalEnv,                       (* no formelEnv update *)
	   printed_vars,
	   vars_to_print,                   (* no more or less variables to print *)
	   Vars.empty                       (* no new slides vars *)
		
       in
       let tl_instrs, ranges, formalEnv, printed_vars, vars_to_print, tl_new_locals = 
	 rewrite_instrs 
	   nodename
	   m
	   constEnv 	  
	   vars_env
	   m 
	   tl_instrs
	   ranges
	   formalEnv
	   printed_vars
	   vars_to_print
	   
       in
       hd_instrs @ tl_instrs,
       ranges,
       formalEnv, 
       printed_vars,
       vars_to_print,
       (Vars.union hd_new_locals tl_new_locals)
     end






(* TODO: deal with new variables, ie. tmp *)
let salsaStep constEnv  m s = 
  let ranges = RangesInt.empty (* empty for the moment, should be build from
				  machine annotations or externally provided information *) in
  let annots = List.fold_left (
    fun accu annl -> 
      List.fold_left (
	fun accu (key, range) ->
	  match key with 
	  | ["salsa"; "ranges"; var] -> (var, range)::accu
	  | _ -> accu
      ) accu annl.LT.annots
  ) [] m.MT.mannot
  in
  let ranges = 
    List.fold_left (fun ranges (v, value) ->
      match value.LT.eexpr_qfexpr.LT.expr_desc with 
      | LT.Expr_tuple [minv; maxv] -> (
	let get_cst e = match e.LT.expr_desc with 
	  | LT.Expr_const (LT.Const_real (c,e,s)) -> 
	    (* calculer la valeur c * 10^e *) 
	    Num.div_num c (Num.power_num (Num.num_of_int 10) (Num.num_of_int e))
	  | _ -> 
	    Format.eprintf 
	      "Invalid salsa range: %a. It should be a pair of constant floats and %a is not a float.@." 
	      Printers.pp_expr value.LT.eexpr_qfexpr
	      Printers.pp_expr e
	    ; 
	    assert false 
	in
	(* let minv = Salsa.Float.Domain.of_num (get_cst minv) and *)
	(*     maxv = Salsa.Float.Domain.of_num (get_cst maxv) in *)
	(* if !debug then Format.eprintf "variable %s in [%s, %s]@ " v (Num.string_of_num minv) (Num.string_of_num maxv); *)
	RangesInt.enlarge ranges v (Salsa.Float.Domain.inject_nums (get_cst minv) (get_cst maxv))
      )
      | _ -> 
	Format.eprintf 
	  "Invalid salsa range: %a. It should be a pair of floats.@." 
	  Printers.pp_expr value.LT.eexpr_qfexpr; 
	assert false
    ) ranges annots
  in
  let formal_env = FormalEnv.empty () in
  let vars_to_print =
    Vars.real_vars  
      (
	Vars.union 
	  (Vars.of_list m.MT.mmemory) 
	  (Vars.of_list s.MT.step_outputs) 
      )
  in 
  (* TODO: should be at least step output + may be memories *)
  
  let vars_env = compute_vars_env m in  
  (* if !debug then Format.eprintf "@[<v 2>Registering node equations@ ";  *)
  let new_instrs, _, _, printed_vars, _, new_locals = 
    rewrite_instrs
      m.MT.mname
      m
      constEnv 
      vars_env
      m
      s.MT.step_instrs
      ranges
      formal_env
      (Vars.real_vars (Vars.of_list s.MT.step_inputs (* printed_vars : real
							inputs are considered as
							already printed *)))
      vars_to_print
      
  in
  let all_local_vars = Vars.real_vars (Vars.of_list s.MT.step_locals) in
  let unused = (Vars.diff all_local_vars printed_vars) in
  let locals =
    if not (Vars.is_empty unused) then (
      if !debug then report ~level:2 (fun fmt -> Format.fprintf fmt  "Unused local vars: [%a]. Removing them.@ "
	Vars.pp unused);
      List.filter (fun v -> not (Vars.mem v unused)) s.MT.step_locals
    )
    else
      s.MT.step_locals
  in
  let locals = locals @ Vars.elements  new_locals in
  { s with MT.step_instrs = new_instrs; MT.step_locals = locals } (* we have also to modify local variables to declare new vars *)


let machine_t2machine_t_optimized_by_salsa constEnv  mt =
  try
    if !debug then report ~level:2 (fun fmt -> Format.fprintf fmt "@[<v 3>Optimizing machine %s@ " mt.MT.mname.LT.node_id);
    let new_step = salsaStep constEnv  mt mt.MT.mstep in
    if !debug then report ~level:2 (fun fmt -> Format.fprintf fmt "@]@ ");
    { mt with MT.mstep = new_step } 
    
      
  with FormalEnv.NoDefinition v as exp -> 
    Format.eprintf "No definition for variable %a@.@?" Printers.pp_var v; 
    raise exp


(* Local Variables: *)
(* compile-command:"make -C ../../.." *)
(* End: *)

