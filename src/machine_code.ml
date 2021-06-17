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
open Spec_types
open Spec_common
open Corelang
open Clocks
open Causality
open Utils

exception NormalizationError

(* Questions:

   - where are used the mconst. They contain initialization of constant in
   nodes. But they do not seem to be used by c_backend *)

(* translate_<foo> : vars -> context -> <foo> -> machine code/expression *)
(* the context contains  m : state aka memory variables  *)
(*                      si : initialization instructions *)
(*                       j : node aka machine instances  *)
(*                       d : local variables             *)
(*                       s : step instructions           *)

(* Machine processing requires knowledge about variables and local variables.
   Local could be memories while other could not. *)
type machine_env = { is_local : string -> bool; get_var : string -> var_decl }

let build_env inputs locals outputs =
  let all = List.sort_uniq VDeclModule.compare (locals @ inputs @ outputs) in
  {
    is_local = (fun id -> List.exists (fun v -> v.var_id = id) locals);
    get_var =
      (fun id ->
        try List.find (fun v -> v.var_id = id) all
        with Not_found ->
          (* Format.eprintf "Impossible to find variable %s in set %a@.@?" * id
             * VSet.pp all; *)
          raise Not_found);
  }

(****************************************************************)
(* Basic functions to translate to machine values, instructions *)
(****************************************************************)

let translate_ident env id =
  (* Format.eprintf "trnaslating ident: %s@." id; *)
  (* id is a var that shall be visible here , ie. in vars *)
  try
    let var_id = env.get_var id in
    vdecl_to_val var_id
  with Not_found -> (
    (* id is a constant *)
    try
      let vdecl =
        Corelang.var_decl_of_const
          (const_of_top (Hashtbl.find Corelang.consts_table id))
      in
      vdecl_to_val vdecl
    with Not_found -> (
      (* id is a tag, getting its type in the list of declared enums *)
      try id_to_tag id
      with Not_found ->
        Format.eprintf "internal error: Machine_code.translate_ident %s@.@?" id;
        assert false))

(* specialize predefined (polymorphic) operators wrt their instances, so that
   the C semantics is preserved *)
let specialize_to_c expr =
  match expr.expr_desc with
  | Expr_appl (id, e, r) ->
    if
      List.exists
        (fun e -> Types.is_bool_type e.expr_type)
        (expr_list_of_expr e)
    then
      let id = match id with "=" -> "equi" | "!=" -> "xor" | _ -> id in
      { expr with expr_desc = Expr_appl (id, e, r) }
    else expr
  | _ ->
    expr

let specialize_op expr =
  match !Options.output with "C" -> specialize_to_c expr | _ -> expr

let rec translate_expr env expr =
  let expr = specialize_op expr in
  let translate_expr = translate_expr env in
  let value_desc =
    match expr.expr_desc with
    | Expr_const v ->
      Cst v
    | Expr_ident x ->
      (translate_ident env x).value_desc
    | Expr_array el ->
      Array (List.map translate_expr el)
    | Expr_access (t, i) ->
      Access (translate_expr t, translate_expr (expr_of_dimension i))
    | Expr_power (e, n) ->
      Power (translate_expr e, translate_expr (expr_of_dimension n))
    | Expr_when (e1, _, _) ->
      (translate_expr e1).value_desc
    | Expr_appl (id, e, _) when Basic_library.is_expr_internal_fun expr ->
      let nd = node_from_name id in
      Fun (node_name nd, List.map translate_expr (expr_list_of_expr e))
    | Expr_ite (g, t, e) when Backends.is_functional () ->
      (* special treatment depending on the active backend. For functional ones,
         like horn backend, ite are preserved in expression. While they are
         removed for C or Java backends. *)
      Fun ("ite", [ translate_expr g; translate_expr t; translate_expr e ])
    | _ ->
      Format.eprintf "Normalization error for backend %s: %a@." !Options.output
        Printers.pp_expr expr;
      raise NormalizationError
  in
  mk_val value_desc expr.expr_type

let translate_guard env expr =
  match expr.expr_desc with
  | Expr_ident x ->
    translate_ident env x
  | _ ->
    Format.eprintf "internal error: translate_guard %a@." Printers.pp_expr expr;
    assert false

let rec translate_act env (y, expr) =
  let translate_act = translate_act env in
  let translate_guard = translate_guard env in
  (* let translate_ident = translate_ident env in *)
  let translate_expr = translate_expr env in
  let lustre_eq = Corelang.mkeq Location.dummy_loc ([ y.var_id ], expr) in
  match expr.expr_desc with
  | Expr_ite (c, t, e) ->
    let c = translate_guard c in
    let t, spec_t = translate_act (y, t) in
    let e, spec_e = translate_act (y, e) in
    mk_conditional ~lustre_eq c [ t ] [ e ], mk_conditional_tr c spec_t spec_e
  | Expr_merge (x, hl) ->
    let var_x = env.get_var x in
    let hl, spec_hl =
      List.(
        split
          (map
             (fun (t, h) ->
               let h, spec_h = translate_act (y, h) in
               (t, [ h ]), (t, spec_h))
             hl))
    in
    mk_branch' ~lustre_eq var_x hl, mk_branch_tr var_x spec_hl
  | _ ->
    let e = translate_expr expr in
    mk_assign ~lustre_eq y e, mk_assign_tr y e

let get_memory env mems eq =
  match eq.eq_lhs, eq.eq_rhs.expr_desc with
  | ([ x ], Expr_pre _ | [ x ], Expr_fby _) when env.is_local x ->
    let var_x = env.get_var x in
    VSet.add var_x mems
  | _ ->
    mems

let get_memories env = List.fold_left (get_memory env) VSet.empty

(* Datastructure updated while visiting equations *)
type machine_ctx = {
  (* memories *)
  m : ISet.t;
  (* Reset instructions *)
  si : instr_t list;
  (* Instances *)
  j : (Lustre_types.top_decl * Dimension.dim_expr list) IMap.t;
  (* Step instructions *)
  s : instr_t list;
  (* Memory pack spec *)
  mp : mc_formula_t list;
  (* Transition spec *)
  t :
    (var_decl list
    (* inputs *)
    * var_decl list
    (* locals *)
    * var_decl list
    (* outputs *)
    * ISet.t (* memory footprint *)
    * mc_formula_t)
    (* formula *)
    list;
}

let ctx_init =
  { m = ISet.empty; si = []; j = IMap.empty; s = []; mp = []; t = [] }

(****************************************************************)
(* Main function to translate equations into this machine context we are
   building *)
(****************************************************************)

let mk_control v l inst = mkinstr (MBranch (vdecl_to_val v, [ l, [ inst ] ]))

let control_on_clock env ck inst =
  let rec aux ((fspec, inst) as acc) ck =
    match (Clocks.repr ck).cdesc with
    | Con (ck, cr, l) ->
      let id = Clocks.const_of_carrier cr in
      let v = env.get_var id in
      aux
        ( (fun spec -> Imply (Equal (Var v, Tag l), fspec spec)),
          mk_control v l inst )
        ck
    | _ ->
      acc
  in
  let fspec, inst = aux ((fun spec -> spec), inst) ck in
  fspec, inst

let reset_instance env i r c =
  match r with
  | Some r ->
    let r = translate_guard env r in
    let _, inst =
      control_on_clock env c
        (mk_conditional r [ mkinstr (MSetReset i) ] [ mkinstr (MNoReset i) ])
    in
    Some r, [ inst ]
  | None ->
    None, []

let translate_eq env ctx id inputs locals outputs i eq =
  let translate_expr = translate_expr env in
  let translate_act = translate_act env in
  let locals_pi = Lustre_live.inter_live_i_with id (i - 1) locals in
  let outputs_pi = Lustre_live.inter_live_i_with id (i - 1) outputs in
  let locals_i = Lustre_live.inter_live_i_with id i locals in
  let outputs_i = Lustre_live.inter_live_i_with id i outputs in
  let pred_mp ctx a = And [ mk_memory_pack ~i:(i - 1) id; a ] :: ctx.mp in
  let pred_t ctx a =
    ( inputs,
      locals_i,
      outputs_i,
      ctx.m,
      Exists
        ( Lustre_live.existential_vars id i eq (locals @ outputs),
          And
            [
              mk_transition ~i:(i - 1) id (vdecls_to_vals inputs)
                (vdecls_to_vals locals_pi)
                (vdecls_to_vals outputs_pi);
              a;
            ] ) )
    :: ctx.t
  in
  let control_on_clock ck inst spec_mp spec_t ctx =
    let fspec, inst = control_on_clock env ck inst in
    {
      ctx with
      s =
        {
          inst with
          instr_spec =
            [
              mk_memory_pack ~i id;
              mk_transition ~i id (vdecls_to_vals inputs)
                (vdecls_to_vals locals_i) (vdecls_to_vals outputs_i);
            ];
        }
        :: ctx.s;
      mp = pred_mp ctx spec_mp;
      t = pred_t ctx (fspec spec_t);
    }
  in
  let reset_instance = reset_instance env in
  let mkinstr' = mkinstr ~lustre_eq:eq in
  let ctl ?(ck = eq.eq_rhs.expr_clock) instr =
    control_on_clock ck (mkinstr' instr)
  in

  (* Format.eprintf "translate_eq %a with clock %a@." Printers.pp_node_eq eq
     Clocks.print_ck eq.eq_rhs.expr_clock; *)
  match eq.eq_lhs, eq.eq_rhs.expr_desc with
  | [ x ], Expr_arrow (e1, e2) ->
    let var_x = env.get_var x in
    let td = Arrow.arrow_top_decl () in
    let inst = new_instance td eq.eq_rhs.expr_tag in
    let c1 = translate_expr e1 in
    let c2 = translate_expr e2 in
    assert (c1.value_desc = Cst (Const_tag "true"));
    assert (c2.value_desc = Cst (Const_tag "false"));
    let ctx =
      ctl
        (MStep ([ var_x ], inst, [ c1; c2 ]))
        (mk_memory_pack ~inst (node_name td))
        (mk_transition ~inst (node_name td) [] [] [ vdecl_to_val var_x ])
        ctx
    in
    {
      ctx with
      si = mkinstr (MSetReset inst) :: ctx.si;
      j = IMap.add inst (td, []) ctx.j;
    }
  | [ x ], Expr_pre e when env.is_local x ->
    let var_x = env.get_var x in
    let e = translate_expr e in
    ctl
      (MStateAssign (var_x, e))
      (mk_state_variable_pack var_x)
      (mk_state_assign_tr var_x e)
      { ctx with m = ISet.add x ctx.m }
  | [ x ], Expr_fby (e1, e2) when env.is_local x ->
    let var_x = env.get_var x in
    let e2 = translate_expr e2 in
    let ctx =
      ctl
        (MStateAssign (var_x, e2))
        (mk_state_variable_pack var_x)
        (mk_state_assign_tr var_x e2)
        { ctx with m = ISet.add x ctx.m }
    in
    {
      ctx with
      si = mkinstr' (MStateAssign (var_x, translate_expr e1)) :: ctx.si;
    }
  | p, Expr_appl (f, arg, r)
    when not (Basic_library.is_expr_internal_fun eq.eq_rhs) ->
    let var_p = List.map (fun v -> env.get_var v) p in
    let el = expr_list_of_expr arg in
    let vl = List.map translate_expr el in
    let node_f = node_from_name f in
    let call_f = node_f, NodeDep.filter_static_inputs (node_inputs node_f) el in
    let inst = new_instance node_f eq.eq_rhs.expr_tag in
    let env_cks =
      List.fold_right
        (fun arg cks -> arg.expr_clock :: cks)
        el [ eq.eq_rhs.expr_clock ]
    in
    let call_ck =
      Clock_calculus.compute_root_clock (Clock_predef.ck_tuple env_cks)
    in
    let r, reset_inst = reset_instance inst r call_ck in
    let ctx =
      ctl ~ck:call_ck
        (MStep (var_p, inst, vl))
        (mk_memory_pack ~inst (node_name node_f))
        (mk_transition ?r ~inst (node_name node_f) vl [] (vdecls_to_vals var_p))
        ctx
    in
    (*Clocks.new_var true in Clock_calculus.unify_imported_clock (Some call_ck)
      eq.eq_rhs.expr_clock eq.eq_rhs.expr_loc; Format.eprintf "call %a: %a:
      %a@," Printers.pp_expr eq.eq_rhs Clocks.print_ck (Clock_predef.ck_tuple
      env_cks) Clocks.print_ck call_ck;*)
    {
      ctx with
      si =
        (if Stateless.check_node node_f then ctx.si
        else mkinstr (MSetReset inst) :: ctx.si);
      j = IMap.add inst call_f ctx.j;
      s = (if Stateless.check_node node_f then [] else reset_inst) @ ctx.s;
    }
  | [ x ], _ ->
    let var_x = env.get_var x in
    let instr, spec = translate_act (var_x, eq.eq_rhs) in
    control_on_clock eq.eq_rhs.expr_clock instr True spec ctx
  | _ ->
    Format.eprintf "internal error: Machine_code.translate_eq %a@?"
      Printers.pp_node_eq eq;
    assert false

let constant_equations locals =
  List.fold_left
    (fun eqs vdecl ->
      if vdecl.var_dec_const then
        {
          eq_lhs = [ vdecl.var_id ];
          eq_rhs = desome vdecl.var_dec_value;
          eq_loc = vdecl.var_loc;
        }
        :: eqs
      else eqs)
    [] locals

let translate_eqs env ctx id inputs locals outputs eqs =
  List.fold_left
    (fun (ctx, i) eq ->
      let ctx = translate_eq env ctx id inputs locals outputs i eq in
      ctx, i + 1)
    (ctx, 1) eqs
  |> fst

(****************************************************************)
(* Processing nodes *)
(****************************************************************)

let process_asserts nd =
  let exprl = List.map (fun assert_ -> assert_.assert_expr) nd.node_asserts in
  if Backends.is_functional () then [], [], exprl
  else
    (* Each assert(e) is associated to a fresh variable v and declared as v=e;
       assert (v); *)
    let _, vars, eql, assertl =
      List.fold_left
        (fun (i, vars, eqlist, assertlist) expr ->
          let loc = expr.expr_loc in
          let var_id = nd.node_id ^ "_assert_" ^ string_of_int i in
          let assert_var =
            mkvar_decl loc ~orig:false
              (* fresh var *)
              ( var_id,
                mktyp loc Tydec_bool,
                mkclock loc Ckdec_any,
                false,
                (* not a constant *)
                None,
                (* no default value *)
                Some nd.node_id )
          in
          assert_var.var_type <- Type_predef.type_bool
          (* Types.new_ty (Types.Tbool) *);
          let eq = mkeq loc ([ var_id ], expr) in
          ( i + 1,
            assert_var :: vars,
            eq :: eqlist,
            { expr with expr_desc = Expr_ident var_id } :: assertlist ))
        (1, [], [], []) exprl
    in
    vars, eql, assertl

let translate_core env nid sorted_eqs inputs locals outputs =
  let constant_eqs = constant_equations locals in

  (* Compute constants' instructions *)
  let ctx0 =
    translate_eqs env ctx_init nid inputs locals outputs constant_eqs
  in
  assert (ctx0.si = []);
  assert (IMap.is_empty ctx0.j);

  (* Compute ctx for all eqs *)
  let ctx = translate_eqs env ctx_init nid inputs locals outputs sorted_eqs in

  ctx, ctx0.s

let zero = mk_val (Cst (Const_int 0)) Type_predef.type_int

let memory_pack_0 nd =
  {
    mpname = nd;
    mpindex = Some 0;
    mpformula =
      And [ StateVarPack ResetFlag; Equal (Memory ResetFlag, Val zero) ];
  }

let memory_pack_toplevel nd i =
  {
    mpname = nd;
    mpindex = None;
    mpformula =
      Ternary
        (Memory ResetFlag, StateVarPack ResetFlag, mk_memory_pack ~i nd.node_id);
  }

let transition_0 nd =
  {
    tname = nd;
    tindex = Some 0;
    tinputs = nd.node_inputs;
    tlocals = [];
    toutputs = [];
    tformula = True;
    tfootprint = ISet.empty;
  }

let transition_toplevel nd i =
  {
    tname = nd;
    tindex = None;
    tinputs = nd.node_inputs;
    tlocals = [];
    toutputs = nd.node_outputs;
    tformula =
      ExistsMem
        ( nd.node_id,
          Predicate (ResetCleared nd.node_id),
          mk_transition nd.node_id ~i
            (vdecls_to_vals nd.node_inputs)
            []
            (vdecls_to_vals nd.node_outputs) );
    tfootprint = ISet.empty;
  }

let translate_decl nd sch =
  (* Format.eprintf "Translating node %s@." nd.node_id; *)
  (* Extracting eqs, variables ..  *)
  let eqs, auts = get_node_eqs nd in
  assert (auts = []);

  (* Automata should be expanded by now *)

  (* In case of non functional backend (eg. C), additional local variables have
     to be declared for each assert *)
  let new_locals, assert_instrs, nd_node_asserts = process_asserts nd in

  (* Build the env: variables visible in the current scope *)
  let locals = nd.node_locals @ new_locals in
  (* let locals = VSet.of_list locals_list in *)
  (* let inout_vars = nd.node_inputs @ nd.node_outputs in *)
  let env = build_env nd.node_inputs locals nd.node_outputs in

  (* Format.eprintf "Node content is %a@." Printers.pp_node nd; *)

  (* Computing main content *)
  (* Format.eprintf "ok1@.@?"; *)
  let schedule = sch.Scheduling_type.schedule in
  (* Format.eprintf "ok2@.@?"; *)
  let sorted_eqs, unused =
    Scheduling.sort_equations_from_schedule eqs schedule
  in

  (* Format.eprintf "ok3@.locals=%a@.inout:%a@?"
   *   VSet.pp locals
   *   VSet.pp inout_vars
   * ; *)
  let equations = assert_instrs @ sorted_eqs in
  let mems = get_memories env equations in
  (* Removing computed memories from locals. We also removed unused variables. *)
  let locals =
    List.filter
      (fun v -> (not (VSet.mem v mems)) && not (List.mem v.var_id unused))
      locals
  in
  (* Compute live sets for spec *)
  Lustre_live.set_live_of nd.node_id nd.node_outputs locals equations;

  (* Translate equations *)
  let ctx, ctx0_s =
    translate_core env nd.node_id equations nd.node_inputs locals
      nd.node_outputs
  in

  (* Format.eprintf "ok4@.@?"; *)

  (* Build the machine *)
  let mmap = IMap.bindings ctx.j in
  let mmemory_packs =
    memory_pack_0 nd
    ::
    List.mapi
      (fun i f -> { mpname = nd; mpindex = Some (i + 1); mpformula = red f })
      (List.rev ctx.mp)
    @ [ memory_pack_toplevel nd (List.length ctx.mp) ]
  in
  let mtransitions =
    transition_0 nd
    ::
    List.mapi
      (fun i (tinputs, tlocals, toutputs, tfootprint, f) ->
        {
          tname = nd;
          tindex = Some (i + 1);
          tinputs;
          tlocals;
          toutputs;
          tformula = red f;
          tfootprint;
        })
      (List.rev ctx.t)
    @ [ transition_toplevel nd (List.length ctx.t) ]
  in
  let clear_reset =
    mkinstr
      ~instr_spec:
        [
          mk_memory_pack ~i:0 nd.node_id;
          mk_transition ~i:0 nd.node_id (vdecls_to_vals nd.node_inputs) [] [];
        ]
      MClearReset
  in
  {
    mname = nd;
    mmemory = VSet.elements mems;
    mcalls = mmap;
    minstances =
      List.filter (fun (_, (n, _)) -> not (Stateless.check_node n)) mmap;
    minit = List.rev ctx.si;
    mconst = List.rev ctx0_s;
    mstatic = List.filter (fun v -> v.var_dec_const) nd.node_inputs;
    mstep =
      {
        step_inputs = nd.node_inputs;
        step_outputs = nd.node_outputs;
        step_locals = locals;
        step_checks =
          List.map
            (fun d ->
              d.Dimension.dim_loc, translate_expr env (expr_of_dimension d))
            nd.node_checks;
        step_instrs =
          clear_reset
          ::
          (* special treatment depending on the active backend. For horn
             backend, common branches are not merged while they are in C or Java
             backends. *)
          (if !Backends.join_guards then join_guards_list (List.rev ctx.s)
          else List.rev ctx.s);
        step_asserts = List.map (translate_expr env) nd_node_asserts;
      };
    (* Processing spec: there is no processing performed here. Contract have
       been processed already. Either one of the other machine is a cocospec
       node, or the current one is a cocospec node. Contract do not contain any
       statement or import. *)
    mspec = { mnode_spec = nd.node_spec; mtransitions; mmemory_packs };
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
        let sch = IMap.find node.node_id node_schs in
        translate_decl node sch)
      nodes
  in
  machines

(* Local Variables: *)
(* compile-command:"make -C .." *)
(* End: *)
