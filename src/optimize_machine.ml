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

open Utils
open Lustre_types
open Spec_types
open Machine_code_types
open Corelang
open Causality
open Machine_code_common
module Mpfr = Lustrec_mpfr

let pp_no_effect fmt = Format.fprintf fmt ".. no effect.@ "

let pp_elim m fmt elim =
  IMap.pp ~comment:"/* elim table: */" (pp_val m) fmt elim

let rec fixpoint f x =
  let y, c = f x in
  if c then fixpoint f y else y

let eliminate_var_decl elim m v a =
  if is_memory m v then a
  else try IMap.find v.var_id elim with Not_found -> a

let rec eliminate_val m elim expr =
  let eliminate_val = eliminate_val m in
  match expr.value_desc with
  | Var v ->
    eliminate_var_decl elim m v expr
  | Fun (id, vl) ->
    { expr with value_desc = Fun (id, List.map (eliminate_val elim) vl) }
  | Array vl ->
    { expr with value_desc = Array (List.map (eliminate_val elim) vl) }
  | Access (v1, v2) ->
    {
      expr with
      value_desc = Access (eliminate_val elim v1, eliminate_val elim v2);
    }
  | Power (v1, v2) ->
    {
      expr with
      value_desc = Power (eliminate_val elim v1, eliminate_val elim v2);
    }
  | Cst _ | ResetFlag ->
    expr

let rec value_eq v1 v2 =
  let values_eq = List.for_all2 value_eq in
  match v1.value_desc, v2.value_desc with
  | Var v1, Var v2 ->
    v1.var_id = v2.var_id
  | Fun (f1, vs1), Fun (f2, vs2) ->
    f1 = f2 && values_eq vs1 vs2
  | Array vs1, Array vs2 ->
    values_eq vs1 vs2
  | Access (v1, v2), Access (w1, w2)
  | Power (v1, v2), Power (w1, w2) ->
    value_eq v1 w1 && value_eq v2 w2
  | v1, v2 -> v1 = v2

let eliminate_val m elim expr =
  let f expr =
    let v = eliminate_val m elim expr in
    let v' = eliminate_val m elim v in
    v, not (value_eq v v')
  in
  fixpoint f expr

let eliminate_expr m elim e =
  let e_val = eliminate_val m elim in
  match e with
  | Val v ->
    Val (e_val v)
  | Var v ->
    Val (e_val (vdecl_to_val v))
  | _ ->
    e

let eliminate_pred m elim = function
  (* the transition is local to the machine *)
  (* | Transition (s, f, inst, Some i, vars, r, mems, insts) -> *)
  (*   let vars = *)
  (*     List.filter_map *)
  (*       (function *)
  (*         | Spec_types.Val v -> ( *)
  (*           match v.value_desc with *)
  (*           | Var vd when IMap.mem vd.var_id elim -> *)
  (*             None *)
  (*           | _ -> *)
  (*             Some (Val v)) *)
  (*         | Spec_types.Var vd when IMap.mem vd.var_id elim -> *)
  (*           None *)
  (*         | e -> *)
  (*           Some (eliminate_expr m elim e)) *)
  (*       vars *)
  (*   in *)
  (*   Transition (s, f, inst, Some i, vars, r, mems, insts) *)
  (* the transition is not local to the machine *)
  | Transition (s, f, inst, i, vars, r, mems, insts) ->
    let vars = List.map (eliminate_expr m elim) vars in
    Transition (s, f, inst, i, vars, r, mems, insts)
  | p ->
    p

let rec eliminate_formula m elim =
  let e_expr = eliminate_expr m elim in
  let e_instr i = eliminate_formula m elim i in
  let e_pred = eliminate_pred m elim in
  function
  | Equal (e1, e2) ->
    Equal (e_expr e1, e_expr e2)
  | GEqual (e1, e2) ->
    GEqual (e_expr e1, e_expr e2)
  | And f ->
    And (List.map e_instr f)
  | Or f ->
    Or (List.map e_instr f)
  | Imply (a, b) ->
    Imply (e_instr a, e_instr b)
  | Exists (xs, a) ->
    let xs = List.filter (fun vd -> not (IMap.mem vd.var_id elim)) xs in
    Exists (xs, e_instr a)
  | Forall (xs, a) ->
    let xs = List.filter (fun vd -> not (IMap.mem vd.var_id elim)) xs in
    Forall (xs, e_instr a)
  | Ternary (e, a, b) ->
    Ternary (e_expr e, e_instr a, e_instr b)
  | Predicate p ->
    Predicate (e_pred p)
  | ExistsMem (f, a, b) ->
    ExistsMem (f, e_instr a, e_instr b)
  | Value v ->
    Value (eliminate_val m elim v)
  | f ->
    f
let eliminate_spec m elim =
  List.map (fun (f, asrt) -> eliminate_formula m elim f, asrt)

let eliminate_spec_instr m elim instr =
  { instr with instr_spec = eliminate_spec m elim instr.instr_spec }

let rec eliminate m elim instr =
  let e_val = eliminate_val m elim in
  let instr = eliminate_spec_instr m elim instr in
  match get_instr_desc instr with
  | MLocalAssign (i, v) ->
    update_instr_desc instr (MLocalAssign (i, e_val v))
  | MStateAssign (i, v) ->
    update_instr_desc instr (MStateAssign (i, e_val v))
  | MSetReset _
  | MNoReset _
  | MClearReset
  | MResetAssign _
  | MSpec _
  | MComment _ ->
    instr
  | MStep (il, i, vl) ->
    update_instr_desc instr (MStep (il, i, List.map e_val vl))
  | MBranch (g, hl) ->
    update_instr_desc
      instr
      (MBranch
         ( e_val g,
           List.map (fun (l, il) -> l, List.map (eliminate m elim) il) hl ))

let rec fv_value m s v =
  match v.value_desc with
  | Var v ->
    if is_memory m v then s else VSet.add v s
  | Fun (_, vl) | Array vl ->
    List.fold_left (fv_value m) s vl
  | Access (v1, v2) | Power (v1, v2) ->
    fv_value m (fv_value m s v1) v2
  | _ ->
    s

let fv_expr m s = function
  | Val v ->
    fv_value m s v
  | Var v ->
    if is_memory m v then s else VSet.add v s
  | _ ->
    s

let fv_predicate m s = function
  | Transition (_, _, _, _, vars, _, _, _) ->
    List.fold_left (fv_expr m) s vars
  | _ ->
    s

let rec fv_formula m s = function
  | Equal (e1, e2) | GEqual (e1, e2) ->
    fv_expr m (fv_expr m s e1) e2
  | And f | Or f ->
    List.fold_left (fv_formula m) s f
  | Imply (a, b) | ExistsMem (_, a, b) ->
    fv_formula m (fv_formula m s a) b
  | Exists (xs, a) | Forall (xs, a) ->
    VSet.filter (fun v -> not (List.mem v xs)) (fv_formula m s a)
  | Ternary (e, a, b) ->
    fv_expr m (fv_formula m (fv_formula m s a) b) e
  | Predicate p ->
    fv_predicate m s p
  | Value v ->
    fv_value m s v
  | _ ->
    s

let eliminate_transition m elim t =
  (* let tvars = List.filter (fun vd -> not (IMap.mem vd.var_id elim)) t.tvars in *)
  let elim = IMap.filter (fun x _ -> not (List.exists (fun v -> v.var_id = x) t.tvars)) elim in
  let tformula = eliminate_formula m elim t.tformula in
  (* let fv = *)
  (*   VSet.(elements (diff (fv_formula m empty tformula) (of_list tvars))) *)
  (* in *)
  (* let tformula = Exists (fv, tformula) in *)
  { t with tformula }


(* XXX: UNUSED *)
(* let eliminate_dim elim dim =
 *   Dimension.expr_replace_expr
 *     (fun v ->
 *       try dimension_of_value (IMap.find v elim)
 *       with Not_found -> mkdim_ident dim.dim_loc v)
 *     dim *)

(* 8th Jan 2016: issues when merging salsa with horn_encoding: The following
   functions seem unsused. They have to be adapted to the new type for expr *)

let unfold_expr_offset m offset expr =
  List.fold_left
    (fun res -> function
      | Index i ->
        mk_val
          (Access (res, value_of_dimension m i))
          (Types.array_element_type res.value_type)
      | Field _ ->
        Format.eprintf "internal error: not yet implemented !";
        assert false)
    expr
    offset

let rec simplify_cst_expr m offset typ cst =
  match offset, cst with
  | [], _ ->
    mk_val (Cst cst) typ
  | Index i :: q, Const_array cl when Dimension.is_const i ->
    let elt_typ = Types.array_element_type typ in
    simplify_cst_expr m q elt_typ (List.nth cl (Dimension.size_const i))
  | Index i :: q, Const_array cl ->
    let elt_typ = Types.array_element_type typ in
    unfold_expr_offset
      m
      [ Index i ]
      (mk_val (Array (List.map (simplify_cst_expr m q elt_typ) cl)) typ)
  | Field f :: q, Const_struct fl ->
    let fld_typ = Types.struct_field_type typ f in
    simplify_cst_expr m q fld_typ (List.assoc f fl)
  | _ ->
    Format.eprintf
      "internal error: Optimize_machine.simplify_cst_expr %a@."
      Printers.pp_const
      cst;
    assert false

let simplify_expr_offset m expr =
  let rec simplify offset expr =
    match offset, expr.value_desc with
    | Field _ :: _, _ ->
      failwith "not yet implemented"
    | _, Fun (id, vl) when Basic_library.is_value_internal_fun expr ->
      mk_val (Fun (id, List.map (simplify offset) vl)) expr.value_type
    | _, Fun _ | _, Var _ ->
      unfold_expr_offset m offset expr
    | _, Cst cst ->
      simplify_cst_expr m offset expr.value_type cst
    | _, Access (expr, i) ->
      simplify (Index (dimension_of_value i) :: offset) expr
    | _, ResetFlag ->
      expr
    | [], _ ->
      expr
    | Index _ :: q, Power (expr, _) ->
      simplify q expr
    | Index i :: q, Array vl when Dimension.is_const i ->
      simplify q (List.nth vl (Dimension.size_const i))
    | Index i :: q, Array vl ->
      unfold_expr_offset
        m
        [ Index i ]
        (mk_val (Array (List.map (simplify q) vl)) expr.value_type)
    (*Format.eprintf "simplify_expr %a %a = %a@." pp_val expr
      (Utils.fprintf_list ~sep:"" Printers.pp_offset) offset pp_val res; res)
      with e -> (Format.eprintf "simplify_expr %a %a = <FAIL>@." pp_val expr
      (Utils.fprintf_list ~sep:"" Printers.pp_offset) offset; raise e*)
  in
  simplify [] expr

let rec simplify_instr_offset m instr =
  match get_instr_desc instr with
  | MLocalAssign (v, expr) ->
    update_instr_desc instr (MLocalAssign (v, simplify_expr_offset m expr))
  | MStateAssign (v, expr) ->
    update_instr_desc instr (MStateAssign (v, simplify_expr_offset m expr))
  | MSetReset _
  | MNoReset _
  | MClearReset
  | MResetAssign _
  | MSpec _
  | MComment _ ->
    instr
  | MStep (outputs, id, inputs) ->
    update_instr_desc
      instr
      (MStep (outputs, id, List.map (simplify_expr_offset m) inputs))
  | MBranch (cond, brl) ->
    update_instr_desc
      instr
      (MBranch
         ( simplify_expr_offset m cond,
           List.map (fun (l, il) -> l, simplify_instrs_offset m il) brl ))

and simplify_instrs_offset m instrs = List.map (simplify_instr_offset m) instrs

(* XXX: UNUSED *)
(* let is_scalar_const c =
 *   match c with Const_real _ | Const_int _ | Const_tag _ -> true | _ -> false *)

(* An instruction v = expr may (and will) be unfolded iff: - either expr is
   atomic (no complex expressions, only const, vars and array/struct accesses) -
   or v has a fanin <= 1 (used at most once) *)
let is_unfoldable_expr fanin expr =
  let rec unfold_const offset cst =
    match offset, cst with
    | _, Const_int _ | _, Const_real _ | _, Const_tag _ ->
      true
    | Field f :: q, Const_struct fl ->
      unfold_const q (List.assoc f fl)
    | [], Const_struct _ ->
      false
    | Index i :: q, Const_array cl when Dimension.is_const i ->
      unfold_const q (List.nth cl (Dimension.size_const i))
    | _, Const_array _ ->
      false
    | _ ->
      assert false
  in
  let rec unfold offset expr =
    match offset, expr.value_desc with
    | _, Cst cst ->
      unfold_const offset cst
    | _, Var _ ->
      true
    | [], Power _ | [], Array _ ->
      false
    | Index _ :: q, Power (v, _) ->
      unfold q v
    | Index i :: q, Array vl when Dimension.is_const i ->
      unfold q (List.nth vl (Dimension.size_const i))
    | _, Array _ ->
      false
    | _, Access (v, i) ->
      unfold (Index (dimension_of_value i) :: offset) v
    | _, Fun (_, vl) when fanin < 2 && Basic_library.is_value_internal_fun expr
      ->
      List.for_all (unfold offset) vl
    | _, Fun _ ->
      false
    | _ ->
      assert false
  in
  unfold [] expr

let basic_unfoldable_assign fanin v expr =
  try
    let d = Hashtbl.find fanin v.var_id in
    is_unfoldable_expr d expr
  with Not_found -> false

let unfoldable_assign fanin v expr =
  (if !Options.mpfr then Mpfr.unfoldable_value expr else true)
  && basic_unfoldable_assign fanin v expr

let merge_elim elim1 elim2 =
  let merge _ e1 e2 =
    match e1, e2 with
    | Some (e1, k1), Some (e2, k2) ->
      Some (e1, e1 = e2 && k1 && k2)
    | _, Some e2 ->
      Some e2
    | Some e1, _ ->
      Some e1
    | _ ->
      None
  in
  IMap.merge merge elim1 elim2


let get_exprs elim = IMap.map (fun (_, e, _) -> e) elim

(* see if elim has to take in account the provided instr: if so, update elim and
   return the remove flag, otherwise, the expression should be kept and elim is
   left untouched *)
let instrs_unfold m fanin elim instrs =
  let rec gather_elim ((elim, instrs) as acc) instr =
    match get_instr_desc instr with
    | MStep ([ v ], id, vl)
      when Basic_library.is_value_internal_fun
             (mk_val (Fun (id, vl)) v.var_type) ->
      gather_elim
        acc
        (update_instr_desc
           instr
           (MLocalAssign (v, mk_val (Fun (id, vl)) v.var_type)))
    | MLocalAssign (v, expr) ->
      let new_eq =
        Corelang.mkeq
          (desome instr.lustre_eq).eq_loc
          ([ v.var_id ], (desome instr.lustre_eq).eq_rhs)
      in
      IMap.add v.var_id ((v, expr, new_eq), true) elim, instr :: instrs
    | MBranch (g, hl) ->
      let elim, hl =
        List.fold_left
          (fun (elim', hl) (h, l) ->
            let elim, l = List.fold_left gather_elim (elim, []) l in
            merge_elim elim' elim, (h, List.rev l) :: hl)
          (elim, [])
          hl
      in
      elim, update_instr_desc instr (MBranch (g, List.rev hl)) :: instrs
    | _ ->
      elim, instr :: instrs
  in
  let elim, instrs = List.fold_left gather_elim (IMap.map (fun x -> x, true) elim, []) instrs in
  (* we don't eliminate clock definitions *)
  let elim = IMap.filter_map (fun _ ((v, e, _ as x), k) ->
      if not (is_clock_dec_type v.var_dec_type.ty_dec_desc)
      && unfoldable_assign fanin v e && k then Some x else None) elim
  in
  let elim_exprs = get_exprs elim in
  let rec filter instrs =
    List.map
      (fun instr ->
        match get_instr_desc instr with
        | MLocalAssign (v, e)
          when (* not (is_clock_dec_type v.var_dec_type.ty_dec_desc) *)
               (* && unfoldable_assign fanin v expr *)
               (* && *) IMap.mem v.var_id elim ->
          (* we transform the assignment into a comment in order to keep its spec *)
          Format.(fprintf str_formatter "%s := %a" v.var_id (pp_val m) e);
          let instr = eliminate_spec_instr m elim_exprs instr in
          update_instr_desc
            instr
            (MComment (Format.flush_str_formatter ()))
        | MBranch (g, hl) ->
          let instr =
            update_instr_desc
              instr
              (MBranch (g, List.map (fun (h, l) -> h, filter l) hl))
          in
          eliminate m elim_exprs instr
        | _ ->
          eliminate m elim_exprs instr)
      instrs
  in
  elim, List.rev (filter instrs)

(** We iterate in the order, recording simple local assigns in an accumulator 1.
    each expression is rewritten according to the accumulator 2. local assigns
    then rewrite occurrences of the lhs in the computed accumulator *)

let static_call_unfold elim (inst, (n, args)) =
  let replace v =
    try dimension_of_value (IMap.find v elim)
    with Not_found -> Dimension.mkdim_ident Location.dummy v
  in
  inst, (n, List.map (Dimension.expr_replace_expr replace) args)

(** Perform optimization on machine code: - iterate through step instructions
    and remove simple local assigns *)
let machine_unfold fanin elim machine =
  let elim_consts, mconst = instrs_unfold machine fanin elim machine.mconst in
  let elim_vars, instrs =
    instrs_unfold machine fanin elim_consts machine.mstep.step_instrs
  in
  Log.report ~level:3 (fun fmt ->
      Format.fprintf
        fmt
        "@[<v 2>machine_unfold %s@;from %a@;to   %a@]@;"
        machine.mname.node_id
        (pp_elim machine)
        (get_exprs elim)
        (pp_elim machine)
        (get_exprs elim_vars));
  let step_instrs = simplify_instrs_offset machine instrs in
  let step_checks =
    List.map
      (fun (loc, check) ->
        loc, eliminate_val machine (get_exprs elim_vars) check)
      machine.mstep.step_checks
  in
  let step_locals =
    List.filter
      (fun v -> not (IMap.mem v.var_id elim_vars))
      machine.mstep.step_locals
  in
  let elim_consts = get_exprs elim_consts in
  let mtransitions =
    List.map
      (eliminate_transition machine elim_consts)
      machine.mspec.mtransitions
  in
  let minstances =
    List.map (static_call_unfold elim_consts) machine.minstances
  in
  let mcalls = List.map (static_call_unfold elim_consts) machine.mcalls in
  ( {
      machine with
      mstep = { machine.mstep with step_locals; step_instrs; step_checks };
      mspec = { machine.mspec with mtransitions };
      mconst;
      minstances;
      mcalls;
    },
    elim_vars )

let instr_of_const top_const =
  let const = const_of_top top_const in
  let loc = const.const_loc in
  let id = const.const_id in
  let vdecl =
    mkvar_decl
      loc
      ( id,
        mktyp Location.dummy Tydec_any,
        mkclock loc Ckdec_any,
        true,
        None,
        None )
  in
  let vdecl = { vdecl with var_type = const.const_type } in
  let lustre_eq =
    mkeq loc ([ const.const_id ], mkexpr loc (Expr_const const.const_value))
  in
  mkinstr
    ~lustre_eq
    (MLocalAssign (vdecl, mk_val (Cst const.const_value) vdecl.var_type))

(* We do not perform this optimization on contract nodes since there is not
   explicit dependence btw variables and their use in contracts. *)
let machines_unfold consts node_schs machines =
  List.fold_right
    (fun m (machines, removed) ->
      let is_contract =
        match m.mspec.mnode_spec with Some (Contract _) -> true | _ -> false
      in
      let m, removed_m =
        if is_contract then m, IMap.empty
        else
          let fanin =
            (IMap.find m.mname.node_id node_schs).Scheduling_type.fanin_table
          in
          let elim_consts, _ =
            instrs_unfold m fanin IMap.empty (List.map instr_of_const consts)
          in
          machine_unfold fanin elim_consts m
      in
      m :: machines, IMap.add m.mname.node_id removed_m removed)
    machines
    ([], IMap.empty)

let get_assign_lhs instr =
  match get_instr_desc instr with
  | MLocalAssign (v, e) ->
    mk_val (Var v) e.value_type
  | MStateAssign (v, e) ->
    mk_val (Var v) e.value_type
  | _ ->
    assert false

let get_assign_rhs instr =
  match get_instr_desc instr with
  | MLocalAssign (_, e) | MStateAssign (_, e) ->
    e
  | _ ->
    assert false

let is_assign instr =
  match get_instr_desc instr with
  | MLocalAssign _ | MStateAssign _ ->
    true
  | _ ->
    false

let mk_assign m v e =
  match v.value_desc with
  | Var v ->
    if is_memory m v then MStateAssign (v, e) else MLocalAssign (v, e)
  | _ ->
    assert false

let rec assigns_instr instr assign =
  match get_instr_desc instr with
  | MLocalAssign (i, _) | MStateAssign (i, _) ->
    VSet.add i assign
  | MStep (ol, _, _) ->
    List.fold_right VSet.add ol assign
  | MBranch (_, hl) ->
    List.fold_right (fun (_, il) -> assigns_instrs il) hl assign
  | _ ->
    assign

and assigns_instrs instrs assign =
  List.fold_left (fun assign instr -> assigns_instr instr assign) assign instrs

(* and substitute_expr subst expr = match expr with | Var v -> (try IMap.find
   expr subst with Not_found -> expr) | Fun (id, vl) -> Fun (id, List.map
   (substitute_expr subst) vl) | Array(vl) -> Array(List.map (substitute_expr
   subst) vl) | Access(v1, v2) -> Access(substitute_expr subst v1,
   substitute_expr subst v2) | Power(v1, v2) -> Power(substitute_expr subst v1,
   substitute_expr subst v2) | Cst _ -> expr *)

(** Finds a substitute for [instr] in [instrs], i.e. another instr' with the
    same rhs expression. Then substitute this expression with the first assigned
    var *)
let subst_instr m subst instrs instr =
  (* Format.eprintf "subst instr: %a@." (pp_instr m) instr; *)
  let instr = eliminate m subst instr in
  let instr_v = get_assign_lhs instr in
  let instr_e = get_assign_rhs instr in
  try
    (* Searching for equivalent asssign *)
    let instr' =
      List.find
        (fun instr' -> is_assign instr' && get_assign_rhs instr' = instr_e)
        instrs
    in
    (* Registering the instr_v as instr'_v while replacing *)
    match instr_v.value_desc with
    | Var v -> (
      let instr'_v = get_assign_lhs instr' in
      if not (is_memory m v) then
        (* The current instruction defines a local variables, ie not memory, we
           can just record the relationship and continue *)
        IMap.add v.var_id instr'_v subst, instrs
      else
        (* The current instruction defines a memory. We need to keep the
           definition, simplified *)
        match instr'_v.value_desc with
        | Var v' ->
          if not (is_memory m v') then
            (* We define v' = v. Don't need to update the records. *)
            let instr =
              eliminate
                m
                subst
                (update_instr_desc instr (mk_assign m instr_v instr'_v))
            in
            subst, instr :: instrs
          else
            (* Last case, v', the lhs of the previous similar definition is,
               itself, a memory *)

            (* TODO regarder avec X. Il me semble qu'on peut faire plus
               simple: *)
            (* Filtering out the list of instructions: - we copy in the same
               order the list of instr in instrs (fold_right) - if the current
               instr is this instr' then apply the elimination with v' -> v on
               instr' before recording it as an instruction. *)
            let subst_v' = IMap.add v'.var_id instr_v IMap.empty in
            let instrs' =
              snd
                (List.fold_right
                   (fun instr (ok, instrs) ->
                     ( ok || instr = instr',
                       if ok then instr :: instrs
                       else if instr = instr' then instrs
                       else eliminate m subst_v' instr :: instrs ))
                   instrs
                   (false, []))
            in
            IMap.add v'.var_id instr_v subst, instr :: instrs'
        | _ ->
          assert false)
    | _ ->
      assert false
  with Not_found ->
    (* No such equivalent expr: keeping the definition *)
    subst, instr :: instrs

(* - [subst] : hashtable from ident to (simple) definition it is an equivalence
   table - [elim] : set of eliminated variables - [instrs] : previous
   instructions, which [instr] is compared against - [instr] : current
   instruction, normalized by [subst] *)

(** Common sub-expression elimination for machine instructions *)
let rec instr_cse m (subst, instrs) instr =
  match get_instr_desc instr with
  (* Simple cases*)
  | MStep ([ v ], id, vl)
    when Basic_library.is_internal_fun id (List.map (fun v -> v.value_type) vl)
    ->
    instr_cse
      m
      (subst, instrs)
      (update_instr_desc
         instr
         (MLocalAssign (v, mk_val (Fun (id, vl)) v.var_type)))
  | MLocalAssign (v, expr) when is_unfoldable_expr 2 expr ->
    IMap.add v.var_id expr subst, instr :: instrs
  | _ when is_assign instr ->
    subst_instr m subst instrs instr
  | _ ->
    subst, instr :: instrs

(** Apply common sub-expression elimination to a sequence of instrs *)
let instrs_cse m subst instrs =
  let subst, rev_instrs = List.fold_left (instr_cse m) (subst, []) instrs in
  subst, List.rev rev_instrs

(** Apply common sub-expression elimination to a machine - iterate through step
    instructions and remove simple local assigns *)
let machine_cse subst machine =
  (*Log.report ~level:1 (fun fmt -> Format.fprintf fmt "machine_cse %a@."
    pp_elim subst);*)
  let _, instrs = instrs_cse machine subst machine.mstep.step_instrs in
  let assigned = assigns_instrs instrs VSet.empty in
  {
    machine with
    mmemory = List.filter (fun (v, _) -> VSet.mem v assigned) machine.mmemory;
    mstep =
      {
        machine.mstep with
        step_locals =
          List.filter
            (fun vdecl -> VSet.mem vdecl assigned)
            machine.mstep.step_locals;
        step_instrs = instrs;
      };
  }

let machines_cse machines = List.map (machine_cse IMap.empty) machines

(* variable substitution for optimizing purposes *)

(* checks whether an [instr] is skip and can be removed from program *)
let rec instr_is_skip instr =
  match get_instr_desc instr with
  | MLocalAssign (i, { value_desc = Var v; _ }) when i = v ->
    true
  | MStateAssign (i, { value_desc = Var v; _ }) when i = v ->
    true
  | MBranch (_, hl) ->
    List.for_all (fun (_, il) -> instrs_are_skip il) hl
  | _ ->
    false

and instrs_are_skip instrs = List.for_all instr_is_skip instrs

let instr_cons instr cont = if instr_is_skip instr then cont else instr :: cont

(* XXX: UNUSED *)
(* let rec instr_remove_skip instr cont =
 *   match get_instr_desc instr with
 *   | MLocalAssign (i, { value_desc = Var v; _ }) when i = v ->
 *     cont
 *   | MStateAssign (i, { value_desc = Var v; _ }) when i = v ->
 *     cont
 *   | MBranch (g, hl) ->
 *     update_instr_desc instr
 *       (MBranch (g, List.map (fun (h, il) -> h, instrs_remove_skip il []) hl))
 *     :: cont
 *   | _ ->
 *     instr :: cont
 *
 * and instrs_remove_skip instrs cont =
 *   List.fold_right instr_remove_skip instrs cont *)

let rec value_replace_var fvar value =
  match value.value_desc with
  | Cst _ | ResetFlag ->
    value
  | Var v ->
    { value with value_desc = Var (fvar v) }
  | Fun (id, args) ->
    { value with value_desc = Fun (id, List.map (value_replace_var fvar) args) }
  | Array vl ->
    { value with value_desc = Array (List.map (value_replace_var fvar) vl) }
  | Access (t, i) ->
    { value with value_desc = Access (value_replace_var fvar t, i) }
  | Power (v, n) ->
    { value with value_desc = Power (value_replace_var fvar v, n) }

let expr_spec_replace fvar = function
  | Val v ->
    Val (value_replace_var fvar v)
  | Var v ->
    Var (fvar v)
  | e ->
    e

let predicate_spec_replace fvar = function
  | Transition (s, f, inst, i, vars, r, mems, insts) ->
    Transition
      (s, f, inst, i, List.map (expr_spec_replace fvar) vars, r, mems, insts)
  | p ->
    p

let is_reused_reassigned m fvar asg v =
  let r_asg = IMap.filter (fun _ n -> n > 1) asg in
  List.exists (fun v' -> v.var_id = v'.var_id) m.mstep.step_locals
  && List.exists (fun v' -> fvar v' = v && v <> v') m.mstep.step_locals
  && IMap.mem v.var_id r_asg

let ghost_vd v =
  { v with var_id = "__" ^ v.var_id }

let rec instr_spec_replace m fvar asg t =
  let aux instr = instr_spec_replace m fvar asg instr in
  (* rename reused vars that appears freely in the formula before substitution, *)
  (* to handle the fact that those vars can be modified in a way that the formula does not hold anymore *)
  let fv_m = VSet.fold (fun v fv_m ->
      if is_reused_reassigned m fvar asg v
      then IMap.add v.var_id (ghost_vd v) fv_m
      else fv_m)  (fv_formula m VSet.empty t) IMap.empty
  in
  let fvar v = try IMap.find v.var_id fv_m with Not_found -> fvar v in
  let t' = match t with
  | Equal (e1, e2) ->
    Equal (expr_spec_replace fvar e1, expr_spec_replace fvar e2)
  | GEqual (e1, e2) ->
    GEqual (expr_spec_replace fvar e1, expr_spec_replace fvar e2)
  | And f ->
    And (List.map aux f)
  | Or f ->
    Or (List.map aux f)
  | Imply (a, b) ->
    Imply (aux a, aux b)
  | Exists (xs, a) ->
    let fvar v = if List.mem v xs then v else fvar v in
    Exists (xs, instr_spec_replace m fvar asg a)
  | Forall (xs, a) ->
    let fvar v = if List.mem v xs then v else fvar v in
    Forall (xs, instr_spec_replace m fvar asg a)
  | Ternary (e, a, b) ->
    Ternary (expr_spec_replace fvar e, aux a, aux b)
  | Predicate p ->
    Predicate (predicate_spec_replace fvar p)
  | ExistsMem (f, a, b) ->
    ExistsMem (f, aux a, aux b)
  | f ->
    f
  in
  (* let fv_t = VSet.of_list (IMap.bindings fv_m |> List.split |> snd) in *)
  (* let fv = VSet.(elements (inter fv_t (fv_formula m empty t'))) in *)
  (* Exists (fv, t') *)
  t'

let add_assigned v =
  IMap.update v.var_id (function
      | Some n -> Some (n + 1)
      | None -> Some 1)

let silly_asg i v = match v.value_desc with
  | Var w -> w.var_id = i.var_id
  | _ -> false

let rec instr_replace_var m fvar (asg, instrs) instr =
  let asg, instr_desc =
    match instr.instr_desc with
    | MLocalAssign (i, v) ->
      let v = value_replace_var fvar v in
      let i = fvar i in
      (if silly_asg i v then asg else add_assigned i asg),
      MLocalAssign (i, v)
    | MStateAssign (i, v) ->
      asg, MStateAssign (i, value_replace_var fvar v)
    | MStep (il, i, vl) ->
      let il = List.map fvar il in
      List.fold_right add_assigned il asg,
      MStep (il, i, List.map (value_replace_var fvar) vl)
    | MBranch (g, hl) ->
      let asg, hl =
        List.fold_left (fun (asg', hl) (h, il) ->
            let asg'', il = instrs_replace_var m fvar asg il in
            (* Format.(printf "%s: before %a after %a@." h (IMap.pp pp_print_int) asg (IMap.pp pp_print_int) asg''); *)
            IMap.union (fun _ n1 n2 -> Some (max n1 n2)) asg' asg'', (h, il) :: hl)
          (IMap.empty, []) hl
      in
      (* Format.(printf "%a@." (IMap.pp pp_print_int) asg); *)
      asg, MBranch ( value_replace_var fvar g, List.rev hl)
    | MSetReset _
    | MNoReset _
    | MClearReset
    | MResetAssign _
    | MSpec _
    | MComment _ ->
      asg, instr.instr_desc
  in
  let instr_spec = List.map (fun (f, asrt) -> instr_spec_replace m fvar asg f, asrt) instr.instr_spec in
  asg, instr_cons { instr with instr_desc; instr_spec } instrs

and instrs_replace_var m fvar asg instrs =
  let asg, instrs = List.fold_left (instr_replace_var m fvar) (asg, []) instrs in
  asg, List.rev instrs

let add_ghost_assign (firsts, spec) v =
  ISet.add v.var_id firsts, (Predicate (GhostAssign (ghost_vd v, v)), false) :: spec

let add_ghost_assigns m fvar asg instrs =
  let rec aux (firsts, instrs) instr =
    let firsts, instr = match instr.instr_desc with
      | MLocalAssign (i, _)
        when is_reused_reassigned m fvar asg i && not (ISet.mem i.var_id firsts) ->
        let firsts, instr_spec = add_ghost_assign (firsts, instr.instr_spec) i in
        firsts, { instr with instr_spec }
      | MStep (il, _, _) ->
        let firsts, instr_spec = List.fold_left (fun (firsts, _ as acc) i ->
            if is_reused_reassigned m fvar asg i && not (ISet.mem i.var_id firsts)
            then add_ghost_assign acc i else acc) (firsts, instr.instr_spec) il
        in
        firsts, { instr with instr_spec }
      | MBranch (g, hl) ->
        let firsts, hl = List.fold_left (fun (firsts', hl) (h, il) ->
            let firsts, il = aux' firsts il in
            ISet.union firsts firsts', ((h, il) :: hl))
            (ISet.empty, []) hl
        in
        firsts, { instr with instr_desc = MBranch (g, List.rev hl) }
      | _ -> firsts, instr
    in
    firsts, instr :: instrs
  and aux' firsts instrs =
    let firsts, instrs = List.fold_left aux (firsts, []) instrs in
    firsts, List.rev instrs
  in
  aux' ISet.empty instrs |> snd

let step_replace_var m fvar step =
  let step_locals =
    List.fold_left
      (fun res l ->
        let l' = fvar l in
        if List.exists (fun o -> o.var_id = l'.var_id) step.step_outputs then res
        else Utils.add_cons l' res)
      []
      step.step_locals
  in
  let step_checks =
    List.map (fun (l, v) -> l, value_replace_var fvar v) step.step_checks
  in
  let asg, step_instrs = instrs_replace_var m fvar IMap.empty step.step_instrs in
  let step_instrs = add_ghost_assigns m fvar asg step_instrs in
  {
    step with
    step_checks;
    step_locals;
    step_instrs
  }

let machine_replace_variables fvar m =
  { m with mstep = step_replace_var m fvar m.mstep }

let pp_reuse fmt reuse =
  Format.fprintf fmt "{ @[<hv>";
  Hashtbl.iter (fun v1 v2 -> Format.fprintf fmt "%s --> %s@ " v1 v2.var_id) reuse;
  Format.fprintf fmt "@]@;}"

let machine_reuse_variables reuse m =
  (* Some outputs may have been replaced by locals. We reverse such bindings. *)
  List.iter (fun out ->
      try
        let x = out.var_id in
        let v = Hashtbl.find reuse x in
        Hashtbl.remove reuse x;
        Hashtbl.add reuse v.var_id out
    with Not_found -> ()) m.mstep.step_outputs;
  Log.report ~level:1 (fun fmt ->
      Format.fprintf
        fmt
        "@[<v 2>.. machine %s reuse table:@,%a@]@,"
        m.mname.node_id
        pp_reuse reuse);
  let fvar v = try Hashtbl.find reuse v.var_id with Not_found -> v in
  let fvar v =
    let f v =
      let v' = fvar v in
      let v'' = fvar v' in
      v', v'.var_id <> v''.var_id
    in
    fixpoint f v
  in
  machine_replace_variables fvar m

let machines_reuse_variables reuse_tables prog =
  Log.report ~level:1 (fun fmt ->
      Format.fprintf
        fmt
        "@,@[<v 2>.. machines optimization: minimize stack usage by reusing \
         variables@,");
  let prog = List.map (fun m ->
      machine_reuse_variables (IMap.find m.mname.node_id reuse_tables) m)
      prog
  in
  Log.report ~level:3 (fun fmt ->
      if IMap.exists (fun _ reuse -> Hashtbl.length reuse <> 0) reuse_tables then
        Format.fprintf
          fmt
          "@[<v 2>.. generated machines (variable reuse):@ %a@]@ "
          pp_machines
          prog
    else pp_no_effect fmt);
  Log.report ~level:1 (fun fmt -> Format.fprintf fmt "@]@,");
  prog

let rec instr_assign res instr =
  match get_instr_desc instr with
  | MLocalAssign (i, _) ->
    Disjunction.CISet.add i res
  | MStateAssign (i, _) ->
    Disjunction.CISet.add i res
  | MBranch (_, hl) ->
    List.fold_left (fun res (_, b) -> instrs_assign res b) res hl
  | MStep (il, _, _) ->
    List.fold_right Disjunction.CISet.add il res
  | _ ->
    res

and instrs_assign res instrs = List.fold_left instr_assign res instrs

let rec instr_constant_assign var instr =
  match get_instr_desc instr with
  | MLocalAssign (i, { value_desc = Cst (Const_tag _); _ })
  | MStateAssign (i, { value_desc = Cst (Const_tag _); _ }) ->
    i = var
  | MBranch (_, hl) ->
    List.for_all (fun (_, b) -> instrs_constant_assign var b) hl
  | _ ->
    false

and instrs_constant_assign var instrs =
  List.fold_left
    (fun res i ->
      if Disjunction.CISet.mem var (instr_assign Disjunction.CISet.empty i) then
        instr_constant_assign var i
      else res)
    false
    instrs

let rec instr_reduce branches instr1 cont =
  match get_instr_desc instr1 with
  | MLocalAssign (_, { value_desc = Cst (Const_tag c); _ })
  | MStateAssign (_, { value_desc = Cst (Const_tag c); _ }) ->
    instr1 :: (List.assoc c branches @ cont)
  | MBranch (g, hl) ->
    update_instr_desc
      instr1
      (MBranch (g, List.map (fun (h, b) -> h, instrs_reduce branches b []) hl))
    :: cont
  | _ ->
    instr1 :: cont

and instrs_reduce branches instrs cont =
  match instrs with
  | [] ->
    cont
  | [ i ] ->
    instr_reduce branches i cont
  | i1 :: i2 :: q ->
    i1 :: instrs_reduce branches (i2 :: q) cont

let rec instrs_fusion instrs =
  match instrs with
  | [] | [ _ ] ->
    false, instrs
  | i1 :: i2 :: q ->
    begin match i2.instr_desc with
      | MBranch ({ value_desc = Var v; _ }, hl) when instr_constant_assign v i1 ->
        true, instr_reduce
          (List.map (fun (h, b) -> h, snd (instrs_fusion b)) hl)
          { i1 with instr_spec = i1.instr_spec @ i2.instr_spec }
          (snd (instrs_fusion q))
      | _ ->
        let b, instrs = instrs_fusion (i2 :: q) in
        b, i1 :: instrs
    end

let step_fusion step =
  let b, step_instrs = instrs_fusion step.step_instrs in
  b, { step with step_instrs }

let machine_fusion m =
  let b, mstep = step_fusion m.mstep in
  b, { m with mstep }

let machines_fusion prog =
  Log.report ~level:1 (fun fmt ->
      Format.fprintf
        fmt
        "@[<v 2>.. machines optimization: enumerated constructors elimination@,");
  let bs, prog = List.(split (map machine_fusion prog)) in
  Log.report ~level:3 (fun fmt ->
      if List.exists (fun b -> b) bs then
        Format.fprintf
          fmt
          "@[<v 2>.. generated machines (enum elim):@ %a@]@ "
          pp_machines
          prog
      else pp_no_effect fmt);
  Log.report ~level:1 (fun fmt -> Format.fprintf fmt "@]@,");
  prog

let machine_clean m =
  let unused = Machine_code_dep.compute_unused_variables m in
  Log.report ~level:1 (fun fmt ->
      Format.fprintf
        fmt
        "@[<v 2>.. machine %s unused variables:@,%a@]@,"
        m.mname.node_id
        ISet.pp unused);
  let is_unused v = ISet.mem v.var_id unused in
  let is_used v = not (ISet.mem v.var_id unused) in
  let step_locals = List.filter is_used m.mstep.step_locals in
  let rec filter_instrs instrs =
    List.filter_map (fun instr ->
        let instr = { instr with
                      instr_spec = List.map (fun (t, asrt) ->
                          let fv = VSet.(elements (filter is_unused (fv_formula m empty t))) in
                          Exists (fv, t), asrt) instr.instr_spec }
        in
        match get_instr_desc instr with
        | MLocalAssign (v, _) ->
          if is_used v then Some instr else None
        | MBranch (e, hl) ->
          Some (update_instr_desc instr
                  (MBranch (e, List.map (fun (h, l) -> h, filter_instrs l) hl)))
        | _ -> Some instr) instrs
  in
  let step_instrs = filter_instrs m.mstep.step_instrs in
  not (ISet.is_empty unused), { m with mstep = { m.mstep with step_locals; step_instrs }}

let machines_clean prog =
  Log.report ~level:1 (fun fmt ->
      Format.fprintf
        fmt
        "@[<v 2>.. machines optimization: cleaning unused variables@,");
  let bs, prog = List.(split (map machine_clean prog)) in
  Log.report ~level:3 (fun fmt ->
      if List.exists (fun b -> b) bs then
        Format.fprintf
          fmt
          "@[<v 2>.. generated machines (cleaning):@ %a@]@ "
          pp_machines
          prog
      else pp_no_effect fmt);
  Log.report ~level:1 (fun fmt -> Format.fprintf fmt "@]@,");
  prog

(* Additional function to modify the prog according to removed variables map *)

let elim_prog_variables prog removed_table =
  List.map
    (fun t ->
      match t.top_decl_desc with
      | Node nd -> (
        match IMap.find_opt nd.node_id removed_table with
        | Some nd_elim_map ->
          (* Iterating through the elim map to compute - the list of variables
             to remove - the associated list of lustre definitions x = expr to
             be used when removing these variables *)
          let vars_to_replace, defs =
            (* Recovering vid from node locals *)
            IMap.fold
              (fun v (_, eq) (accu_locals, accu_defs) ->
                let locals =
                  try
                    List.find (fun v' -> v'.var_id = v) (List.map fst nd.node_locals)
                    :: accu_locals
                  with Not_found -> accu_locals
                  (* Variable v shall be a global constant, we do no need to
                     eliminate it from the locals *)
                in
                (* xxx let new_eq = { eq_lhs = [v]; eq_rhs = e; eq_loc =
                   e.expr_loc } in *)
                let defs = eq :: accu_defs in
                locals, defs)
              nd_elim_map
              ([], [])
          in
          let node_locals, node_stmts =
            List.fold_right
              (fun stmt (locals, res_stmts) ->
                match stmt with
                | Aut _ ->
                  assert false (* should be processed by now *)
                | Eq eq -> (
                  match eq.eq_lhs with
                  | [] ->
                    assert false (* shall not happen *)
                  | [ lhs ]
                    when List.exists (fun v -> v.var_id = lhs) vars_to_replace
                    ->
                    (* We remove the def *)
                    List.filter (fun (v, _) -> v.var_id <> lhs) locals, res_stmts
                  | _ ->
                    (* When more than one lhs we just keep the equation and do
                       not delete it *)
                    let eq_rhs =
                      substitute_expr vars_to_replace defs eq.eq_rhs
                    in
                    locals, Eq { eq with eq_rhs } :: res_stmts))
              nd.node_stmts
              (nd.node_locals, [])
          in
          let nd' = { nd with node_locals; node_stmts } in
          { t with top_decl_desc = Node nd' }
        | None ->
          t)
      | _ ->
        t)
    prog

(*** Main function ***)

(* This functions produces an optimzed prog * machines It 1- eliminates common
   sub-expressions (TODO how is this different from normalization?) 2- inline
   constants and eliminate duplicated variables 3- try to reuse variables
   whenever possible

   When item (2) identified eliminated variables, the initial prog is modified,
   its normalized recomputed, as well as its scheduling, before regenerating the
   machines.

   The function returns both the (possibly updated) prog as well as the
   machines *)
let optimize params prog node_schs machine_code =
  let machine_code =
    if !Options.optimization >= 4 (* && !Options.output <> "horn" *) then (
      Log.report ~level:1 (fun fmt ->
          Format.fprintf
            fmt
            "@ @[<v 2>.. machines optimization: sub-expression elimination@ ");
      let machine_code = machines_cse machine_code in
      Log.report ~level:3 (fun fmt ->
          Format.fprintf
            fmt
            "@[<v 2>.. generated machines (sub-expr elim):@ %a@]@ "
            pp_machines
            machine_code);
      Log.report ~level:1 (fun fmt -> Format.fprintf fmt "@]");
      machine_code)
    else machine_code
  in
  (* Optimize machine code *)
  let prog, machine_code, removed_table =
    if
      !Options.optimization >= 2 && !Options.output <> Options.OutEMF
      (*&& !Options.output <> "horn"*)
    then (
      Log.report ~level:1 (fun fmt ->
          Format.fprintf
            fmt
            "@ @[<v 2>.. machines optimization: const. inlining (partial eval. \
             with const)@ ");
      let machine_code, removed_table =
        machines_unfold (Corelang.get_consts prog) node_schs machine_code
      in
      Log.report ~level:3 (fun fmt ->
          Format.fprintf
            fmt
            "@ Eliminated flows: %a@ "
            (IMap.pp (fun fmt m -> pp_elim empty_machine fmt (get_exprs m)))
            removed_table);
      (* If variables were eliminated, relaunch the normalization/machine
         generation *)
      (* let prog, machine_code, removed_table = *)
      (*   if IMap.is_empty removed_table then *)
      (*     (\* stopping here, no need to reupdate the prog *\) *)
      (*     prog, machine_code, removed_table *)
      (*   else *)
      (*     let prog = elim_prog_variables prog removed_table in *)
      (*     (\* Mini stage1 *\) *)
      (*     let prog = Normalization.normalize_prog ~first:false params prog in *)
      (*     let prog = SortProg.sort_nodes_locals prog in *)
      (*     (\* Mini stage2: note that we do not protect against alg. loop since *)
      (*        this should have been handled before *\) *)
      (*     let prog, node_schs = Scheduling.schedule_prog prog in *)
      (*     let machine_code = Machine_code.translate_prog prog node_schs in *)
      (*     (\* Mini stage2 machine optimiation *\) *)
      (*     let machine_code, removed_table = *)
      (*       machines_unfold (Corelang.get_consts prog) node_schs machine_code *)
      (*     in *)
      (*     prog, machine_code, removed_table *)
      (* in *)
      Log.report ~level:3 (fun fmt ->
          Format.fprintf
            fmt
            "@ @[<v 2>.. generated machines (const inlining):@ %a@]@ "
            pp_machines
            machine_code);
      Log.report ~level:1 (fun fmt -> Format.fprintf fmt "@]");
      prog, machine_code, removed_table)
    else prog, machine_code, IMap.empty
  in
  (* Optimize machine code *)
  let machine_code =
    if !Options.optimization >= 3 && not (Backends.is_functional ()) then
      let node_schs =
        Scheduling.remove_prog_inlined_locals removed_table node_schs
      in
      let reuse_tables = Scheduling.compute_prog_reuse_table node_schs in
      machine_code
      |> machines_reuse_variables reuse_tables
      |> machines_fusion
      |> machines_clean
    else machine_code
  in

  prog, machine_code

(* Local Variables: *)
(* compile-command:"make -C .." *)
(* End: *)
