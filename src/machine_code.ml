(********************************************************************)
(*                                                                  *)
(*  The LustreC compiler toolset   /  The LustreC Development Team  *)
(*  Copyright 2012 -    --   ONERA - CNRS - INPT                    *)
(*                                                                  *)
(*  LustreC is free software, distributed WITHOUT ANY WARRANTY      *)
(*  under the terms of the GNU Lesser General Public License        *)
(*  version 2.1.                                                    *)
(*                                                                  *)
(********************************************************************)

open Lustre_types
open Machine_code_types
open Machine_code_common
open Corelang
open Clocks
open Causality
  
exception NormalizationError

(* Questions:

   - where are used the mconst. They contain initialization of
   constant in nodes. But they do not seem to be used by c_backend *)

       
(* translate_<foo> : vars -> context -> <foo> -> machine code/expression *)
(* the context contains  m : state aka memory variables  *)
(*                      si : initialization instructions *)
(*                       j : node aka machine instances  *)
(*                       d : local variables             *)
(*                       s : step instructions           *)

(* Machine processing requires knowledge about variables and local
   variables. Local could be memories while other could not.  *)
type machine_env = {
    is_local: string -> bool;
    get_var: string -> var_decl
  }

                 
let build_env locals non_locals =
  let all = VSet.union locals non_locals in
  {
    is_local = (fun id -> VSet.exists (fun v -> v.var_id = id) locals);
    get_var = (fun id -> try
                  VSet.get id all
                with Not_found -> (
                  (* Format.eprintf "Impossible to find variable %s in set %a@.@?"
                   *   id
                   *   VSet.pp all; *)
                  raise Not_found
                )
              )  
  }

  

(****************************************************************)
(* Basic functions to translate to machine values, instructions *) 
(****************************************************************)

let translate_ident env id =
  (* Format.eprintf "trnaslating ident: %s@." id; *)
  try (* id is a var that shall be visible here , ie. in vars *)
    let var_id = env.get_var id in
    mk_val (Var var_id) var_id.var_type
  with Not_found ->
    try (* id is a constant *)
      let vdecl = (Corelang.var_decl_of_const
                     (const_of_top (Hashtbl.find Corelang.consts_table id)))
      in
      mk_val (Var vdecl) vdecl.var_type
    with Not_found ->
      (* id is a tag, getting its type in the list of declared enums *)
      try
        let typ = (typedef_of_top (Hashtbl.find Corelang.tag_table id)).tydef_id in
        mk_val (Cst (Const_tag id)) (Type_predef.type_const typ)
      with Not_found -> (Format.eprintf
                           "internal error: Machine_code.translate_ident %s@.@?"
                           id;
                         assert false)

let rec control_on_clock env ck inst =
 match (Clocks.repr ck).cdesc with
 | Con    (ck1, cr, l) ->
   let id  = Clocks.const_of_carrier cr in
   control_on_clock env ck1
     (mkinstr
	(MBranch (translate_ident env id,
		  [l, [inst]] )))
 | _                   -> inst


(* specialize predefined (polymorphic) operators wrt their instances,
   so that the C semantics is preserved *)
let specialize_to_c expr =
 match expr.expr_desc with
 | Expr_appl (id, e, r) ->
   if List.exists (fun e -> Types.is_bool_type e.expr_type) (expr_list_of_expr e)
   then let id =
	  match id with
	  | "="  -> "equi"
	  | "!=" -> "xor"
	  | _    -> id in
	{ expr with expr_desc = Expr_appl (id, e, r) }
   else expr
 | _ -> expr

let specialize_op expr =
  match !Options.output with
  | "C" -> specialize_to_c expr
  | _   -> expr

let rec translate_expr env expr =
  let expr = specialize_op expr in
  let translate_expr = translate_expr env in
  let value_desc = 
    match expr.expr_desc with
    | Expr_const v                     -> Cst v
    | Expr_ident x                     -> (translate_ident env x).value_desc
    | Expr_array el                    -> Array (List.map translate_expr el)
    | Expr_access (t, i)               -> Access (translate_expr t,
                                                  translate_expr 
                                                    (expr_of_dimension i))
    | Expr_power  (e, n)               -> Power  (translate_expr e,
                                                  translate_expr
                                                    (expr_of_dimension n))
    | Expr_tuple _
      | Expr_arrow _ 
      | Expr_fby _
      | Expr_pre _                       -> (Printers.pp_expr
                                               Format.err_formatter expr;
                                             Format.pp_print_flush
                                               Format.err_formatter ();
                                             raise NormalizationError)
                                          
    | Expr_when    (e1, _, _)          -> (translate_expr e1).value_desc
    | Expr_merge   (x, _)              -> raise NormalizationError
    | Expr_appl (id, e, _) when Basic_library.is_expr_internal_fun expr ->
       let nd = node_from_name id in
       Fun (node_name nd, List.map translate_expr (expr_list_of_expr e))
    | Expr_ite (g,t,e) -> (
      (* special treatment depending on the active backend. For
         functional ones, like horn backend, ite are preserved in
         expression. While they are removed for C or Java backends. *)
      if Backends.is_functional () then
	Fun ("ite", [translate_expr g; translate_expr t; translate_expr e])
      else 
	(Format.eprintf "Normalization error for backend %s: %a@."
	   !Options.output
	   Printers.pp_expr expr;
	 raise NormalizationError)
    )
    | _                   -> raise NormalizationError
  in
  mk_val value_desc expr.expr_type

let translate_guard env expr =
  match expr.expr_desc with
  | Expr_ident x  -> translate_ident env x
  | _ -> (Format.eprintf "internal error: translate_guard %a@."
            Printers.pp_expr expr;
          assert false)

let rec translate_act env (y, expr) =
  let translate_act = translate_act env in
  let translate_guard = translate_guard env in
  let translate_ident = translate_ident env in
  let translate_expr = translate_expr env in
  let eq = Corelang.mkeq Location.dummy_loc ([y.var_id], expr) in
  match expr.expr_desc with
  | Expr_ite   (c, t, e) -> let g = translate_guard c in
			    mk_conditional ?lustre_eq:(Some eq) g
                              [translate_act (y, t)]
                              [translate_act (y, e)]
  | Expr_merge (x, hl)   -> mkinstr ?lustre_eq:(Some eq)
                              (MBranch (translate_ident x,
                                        List.map (fun (t,  h) ->
                                            t, [translate_act (y, h)])
                                          hl))
  | _                    -> mkinstr ?lustre_eq:(Some eq)
                              (MLocalAssign (y, translate_expr expr))

let reset_instance env i r c =
  match r with
  | None        -> []
  | Some r      -> let g = translate_guard env r in
                   [control_on_clock
                      env
                      c
                      (mk_conditional
                         g
                         [mkinstr (MReset i)]
                         [mkinstr (MNoReset i)])
                   ]


(* Datastructure updated while visiting equations *)
type machine_ctx = {
    m: VSet.t; (* Memories *)
    si: instr_t list;
    j: (Lustre_types.top_decl * Dimension.dim_expr list) Utils.IMap.t;
    s: instr_t list;
  }

let ctx_init = { m = VSet.empty; (* memories *)
                 si = []; (* init instr *)
                 j = Utils.IMap.empty;
                 s = [] }
             
(****************************************************************)
(* Main function to translate equations into this machine context we
   are building *) 
(****************************************************************)

                   

let translate_eq env ctx eq =
  let translate_expr = translate_expr env in
  let translate_act = translate_act env in
  let control_on_clock = control_on_clock env in
  let reset_instance = reset_instance env in

  (* Format.eprintf "translate_eq %a with clock %a@." 
     Printers.pp_node_eq eq Clocks.print_ck eq.eq_rhs.expr_clock;  *)
  match eq.eq_lhs, eq.eq_rhs.expr_desc with
  | [x], Expr_arrow (e1, e2)                     ->
     let var_x = env.get_var x in
     let o = new_instance Arrow.arrow_top_decl eq.eq_rhs.expr_tag in
     let c1 = translate_expr e1 in
     let c2 = translate_expr e2 in
     { ctx with
       si = mkinstr (MReset o) :: ctx.si;
       j = Utils.IMap.add o (Arrow.arrow_top_decl, []) ctx.j;
       s = (control_on_clock
              eq.eq_rhs.expr_clock
              (mkinstr ?lustre_eq:(Some eq) (MStep ([var_x], o, [c1;c2])))
           ) :: ctx.s
     }
  | [x], Expr_pre e1 when env.is_local x    ->
     let var_x = env.get_var x in
     
      { ctx with
        m = VSet.add var_x ctx.m;
        s = control_on_clock
              eq.eq_rhs.expr_clock
              (mkinstr ?lustre_eq:(Some eq)
                 (MStateAssign (var_x, translate_expr e1)))
            :: ctx.s
      }
  | [x], Expr_fby (e1, e2) when env.is_local x ->
     let var_x = env.get_var x in
     { ctx with
       m = VSet.add var_x ctx.m;
       si = mkinstr ?lustre_eq:(Some eq)
              (MStateAssign (var_x, translate_expr e1))
            :: ctx.si;
       s = control_on_clock
             eq.eq_rhs.expr_clock
             (mkinstr ?lustre_eq:(Some eq)
                (MStateAssign (var_x, translate_expr e2)))
           :: ctx.s
     }

  | p  , Expr_appl (f, arg, r) when not (Basic_library.is_expr_internal_fun eq.eq_rhs) ->
     let var_p = List.map (fun v -> env.get_var v) p in
     let el = expr_list_of_expr arg in
     let vl = List.map translate_expr el in
     let node_f = node_from_name f in
     let call_f =
       node_f,
       NodeDep.filter_static_inputs (node_inputs node_f) el in
     let o = new_instance node_f eq.eq_rhs.expr_tag in
     let env_cks = List.fold_right (fun arg cks -> arg.expr_clock :: cks) el [eq.eq_rhs.expr_clock] in
     let call_ck = Clock_calculus.compute_root_clock (Clock_predef.ck_tuple env_cks) in
     (*Clocks.new_var true in
       Clock_calculus.unify_imported_clock (Some call_ck) eq.eq_rhs.expr_clock eq.eq_rhs.expr_loc;
       Format.eprintf "call %a: %a: %a@," Printers.pp_expr eq.eq_rhs Clocks.print_ck (Clock_predef.ck_tuple env_cks) Clocks.print_ck call_ck;*)
     { ctx with
       si = 
         (if Stateless.check_node node_f then ctx.si else mkinstr (MReset o) :: ctx.si);
      j = Utils.IMap.add o call_f ctx.j;
      s = (if Stateless.check_node node_f
           then []
           else reset_instance o r call_ck) @
	    (control_on_clock call_ck
               (mkinstr ?lustre_eq:(Some eq) (MStep (var_p, o, vl))))
            :: ctx.s
     }

  | [x], _                                       -> (
    let var_x = env.get_var x in
    { ctx with
      s = 
     control_on_clock 
       eq.eq_rhs.expr_clock
       (translate_act (var_x, eq.eq_rhs)) :: ctx.s
    }
  )
  | _                                            ->
     begin
       Format.eprintf "internal error: Machine_code.translate_eq %a@?"
         Printers.pp_node_eq eq;
       assert false
     end



let constant_equations locals =
 VSet.fold (fun vdecl eqs ->
   if vdecl.var_dec_const
   then
     { eq_lhs = [vdecl.var_id];
       eq_rhs = Utils.desome vdecl.var_dec_value;
       eq_loc = vdecl.var_loc
     } :: eqs
   else eqs)
   locals []

let translate_eqs env ctx eqs =
  List.fold_right (fun eq ctx -> translate_eq env ctx eq) eqs ctx;;


(****************************************************************)
(* Processing nodes *) 
(****************************************************************)

let process_asserts nd =
  
    let exprl = List.map (fun assert_ -> assert_.assert_expr ) nd.node_asserts in
    if Backends.is_functional () then
      [], [], exprl  
    else (* Each assert(e) is associated to a fresh variable v and declared as
	    v=e; assert (v); *)
      let _, vars, eql, assertl =
	List.fold_left (fun (i, vars, eqlist, assertlist) expr ->
	  let loc = expr.expr_loc in
	  let var_id = nd.node_id ^ "_assert_" ^ string_of_int i in
	  let assert_var =
	    mkvar_decl
	      loc
	      ~orig:false (* fresh var *)
	      (var_id,
	       mktyp loc Tydec_bool,
	       mkclock loc Ckdec_any,
	       false, (* not a constant *)
	       None, (* no default value *)
	       Some nd.node_id
	      )
	  in
	  assert_var.var_type <- Type_predef.type_bool (* Types.new_ty (Types.Tbool) *); 
	  let eq = mkeq loc ([var_id], expr) in
          (i+1,
           assert_var::vars,
           eq::eqlist,
           {expr with expr_desc = Expr_ident var_id}::assertlist)
	) (1, [], [], []) exprl
      in
      vars, eql, assertl

let translate_core sorted_eqs locals other_vars =
  let constant_eqs = constant_equations locals in
  
  let env = build_env locals other_vars  in
  
  (* Compute constants' instructions  *)
  let ctx0 = translate_eqs env ctx_init constant_eqs in
  assert (VSet.is_empty ctx0.m);
  assert (ctx0.si = []);
  assert (Utils.IMap.is_empty ctx0.j);
  
  (* Compute ctx for all eqs *)
  let ctx = translate_eqs env ctx_init sorted_eqs in
  
  ctx, ctx0.s

 
let translate_decl nd sch =
  (* Format.eprintf "Translating node %s@." nd.node_id; *)
  (* Extracting eqs, variables ..  *)
  let eqs, auts = get_node_eqs nd in
  assert (auts = []); (* Automata should be expanded by now *)
  
  (* In case of non functional backend (eg. C), additional local variables have
     to be declared for each assert *)
  let new_locals, assert_instrs, nd_node_asserts = process_asserts nd in

  (* Build the env: variables visible in the current scope *)
  let locals_list = nd.node_locals @ new_locals in
  let locals = VSet.of_list locals_list in
  let inout_vars = (VSet.of_list (nd.node_inputs @ nd.node_outputs)) in
  let env = build_env locals inout_vars  in 

  (* Format.eprintf "Node content is %a@." Printers.pp_node nd; *)
  
  (* Computing main content *)
  (* Format.eprintf "ok1@.@?"; *)
  let schedule = sch.Scheduling_type.schedule in
  (* Format.eprintf "ok2@.@?"; *)
  let sorted_eqs, unused = Scheduling.sort_equations_from_schedule eqs schedule in
  (* Format.eprintf "ok3@.locals=%a@.inout:%a@?"
   *   VSet.pp locals
   *   VSet.pp inout_vars
   * ; *)
  
  let ctx, ctx0_s = translate_core (assert_instrs@sorted_eqs) locals inout_vars in
  
  (* Format.eprintf "ok4@.@?"; *)

  (* Removing computed memories from locals. We also removed unused variables. *)
  let updated_locals =
    let l = VSet.elements (VSet.diff locals ctx.m) in
    List.fold_left (fun res v -> if List.mem v.var_id unused then res else v::res) [] l
  in
  let mmap = Utils.IMap.elements ctx.j in
  {
    mname = nd;
    mmemory = VSet.elements ctx.m;
    mcalls = mmap;
    minstances = List.filter (fun (_, (n,_)) -> not (Stateless.check_node n)) mmap;
    minit = ctx.si;
    mconst = ctx0_s;
    mstatic = List.filter (fun v -> v.var_dec_const) nd.node_inputs;
    mstep = {
        step_inputs = nd.node_inputs;
        step_outputs = nd.node_outputs;
        step_locals = updated_locals;
        step_checks = List.map (fun d -> d.Dimension.dim_loc,
                                         translate_expr env 
                                           (expr_of_dimension d))
                        nd.node_checks;
        step_instrs = (
	  (* special treatment depending on the active backend. For horn backend,
	   common branches are not merged while they are in C or Java
	   backends. *)
	  if !Backends.join_guards then
	    join_guards_list ctx.s
	  else
	    ctx.s
        );
        step_asserts = List.map (translate_expr env) nd_node_asserts;
      };

    (* Processing spec: there is no processing performed here. Contract
     have been processed already. Either one of the other machine is a
     cocospec node, or the current one is a cocospec node. Contract do
     not contain any statement or import. *)
 
    mspec = nd.node_spec;
    mannot = nd.node_annot;
    msch = Some sch;
  }

(** takes the global declarations and the scheduling associated to each node *)
let translate_prog decls node_schs =
  let nodes = get_nodes decls in
  let machines =
    List.map
    (fun decl ->
     let node = node_of_top decl in
      let sch = Utils.IMap.find node.node_id node_schs in
      translate_decl node sch
    ) nodes
  in
  machines

    (* Local Variables: *)
    (* compile-command:"make -C .." *)
    (* End: *)
