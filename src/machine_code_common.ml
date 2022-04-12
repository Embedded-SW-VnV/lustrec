open Lustre_types
open Machine_code_types
open Spec_types
open Corelang
open Utils
open Format

let print_statelocaltag = true

let find_tainter_arrow m id =
  List.find_opt (fun (x, _) -> x.var_id = id.var_id) m.mmemory
  |> Option.map snd

let is_memory m id =
  Option.is_some (find_tainter_arrow m id)

let is_reset_flag id = id.var_id = "_reset"

let pp_vdecl fmt v = pp_print_string fmt v.var_id

let rec pp_val m fmt v =
  let pp_val = pp_val m in
  match v.value_desc with
  | Cst c ->
    Printers.pp_const fmt c
  | Var v ->
    if is_memory m v then
      if print_statelocaltag then fprintf fmt "{%s}" v.var_id
      else pp_print_string fmt v.var_id
    else if print_statelocaltag then fprintf fmt "%s" v.var_id
    else pp_vdecl fmt v
  | Array vl ->
    pp_print_bracketed pp_val fmt vl
  | Access (t, i) ->
    fprintf fmt "%a[%a]" pp_val t pp_val i
  | Power (v, n) ->
    fprintf fmt "(%a^%a)" pp_val v pp_val n
  | Fun (n, vl) ->
    fprintf fmt "%s%a" n (pp_print_parenthesized pp_val) vl
  | ResetFlag ->
    fprintf fmt "RESET"

module PrintSpec = struct
  let pp_reg fmt = function
    | ResetFlag ->
      pp_print_string fmt "{RESET}"
    | StateVar v ->
      fprintf fmt "{OUT:%a}" pp_vdecl v

  let pp_expr m fmt = function
    | Val v ->
      pp_val m fmt v
    | Tag (t, _) ->
      pp_print_string fmt t
    | Var v ->
      pp_vdecl fmt v
    | Memory r ->
      pp_reg fmt r

  let pp_predicate m fmt p =
    let pp_expr fmt e = pp_expr m fmt e in
    match p with
    | Transition (_, f, inst, i, vars, _r, _mems, _insts) ->
      fprintf
        fmt
        "Transition_%a<%a>%a%a"
        pp_print_string
        f
        (pp_print_option
           ~none:(fun fmt () -> pp_print_string fmt "SELF")
           pp_print_string)
        inst
        (pp_print_option pp_print_int)
        i
        (pp_print_parenthesized pp_expr)
        vars
    | Reset (f, inst, r) ->
      fprintf
        fmt
        "Reset_%a<%a> on %a"
        pp_print_string
        f
        pp_print_string
        inst
        (pp_val m)
        r
    | MemoryPackBase f ->
      fprintf
        fmt
        "MemoryPackBase_%a"
        pp_print_string
        f
    | MemoryPack (f, inst, i) ->
      fprintf
        fmt
        "MemoryPack_%a<%a>%a"
        pp_print_string
        f
        (pp_print_option
           ~none:(fun fmt () -> pp_print_string fmt "SELF")
           pp_print_string)
        inst
        (pp_print_option pp_print_int)
        i
    | ResetCleared f ->
      fprintf fmt "ResetCleared_%a" pp_print_string f
    | Initialization ->
      ()
    | GhostAssign (v1, v2) ->
      fprintf fmt "Ghost %s = %s" v1.var_id v2.var_id

  let pp_spec m =
    let pp_expr fmt e = pp_expr m fmt e in
    let rec pp_spec fmt f =
      match f with
      | True ->
        pp_print_string fmt "true"
      | False ->
        pp_print_string fmt "false"
      | Equal (a, b) ->
        fprintf fmt "%a == %a" pp_expr a pp_expr b
      | GEqual (a, b) ->
        fprintf fmt "%a >= %a" pp_expr a pp_expr b
      | And fs ->
        pp_print_list
          ~pp_sep:(fun fmt () -> fprintf fmt "@ ∧ ")
          (fun fmt spec -> fprintf fmt "@[%a@]" pp_spec spec)
          fmt
          fs
      | Or fs ->
        pp_print_list
          ~pp_sep:(fun fmt () -> fprintf fmt "@ ∨ ")
          (fun fmt spec -> fprintf fmt "@[%a@]" pp_spec spec)
          fmt
          fs
      | Imply (a, b) ->
        fprintf fmt "%a@ -> %a" pp_spec a pp_spec b
      | Exists (xs, a) ->
        fprintf
          fmt
          "@[<hv 2>∃ @[<h>%a,@]@ %a@]"
          (pp_comma_list Printers.pp_var)
          xs
          pp_spec
          a
      | Forall (xs, a) ->
        fprintf
          fmt
          "@[<hv 2>∀ @[<h>%a,@]@ %a@]"
          (pp_comma_list Printers.pp_var)
          xs
          pp_spec
          a
      | Ternary (e, a, b) ->
        fprintf
          fmt
          "If %a Then (@[<hov>%a@]) Else (@[<hov>%a@])"
          pp_expr
          e
          pp_spec
          a
          pp_spec
          b
      | Predicate p ->
        pp_predicate m fmt p
      | StateVarPack (r, tainted) ->
        fprintf fmt "StateVarPack%a<%a>"
          (if tainted then pp_print_string else pp_print_nothing) "_tainted"
          pp_reg r
      | ExistsMem (_f, a, b) ->
        fprintf fmt "@[<hv 2>∃ MEM,@ %a@]" pp_spec (And [ a; b ])
      | Value v ->
        pp_val m fmt v
    in

    pp_spec
end

let pp_spec m =
  match !Options.spec with
  | Options.SpecNo ->
    pp_print_nothing
  | _ ->
    pp_print_list
      ~pp_open_box:pp_open_vbox0
      ~pp_prologue:pp_print_cut
      (fun fmt (spec, _) -> fprintf fmt "@[<h>--%@ %a@]" (PrintSpec.pp_spec m) spec)

let rec pp_instr m fmt i =
  let pp_val = pp_val m in
  let pp_branch = pp_branch m in
  (match i.instr_desc with
  | MLocalAssign (i, v) ->
    fprintf fmt "%s := %a" i.var_id pp_val v
  | MStateAssign (i, v) ->
    fprintf fmt "{%s} := %a" i.var_id pp_val v
  | MResetAssign b ->
    fprintf fmt "RESET := %a" pp_print_bool b
  | MSetReset i ->
    fprintf fmt "set_reset %s" i
  | MClearReset ->
    fprintf fmt "clear_reset %s" m.mname.node_id
  | MNoReset i ->
    fprintf fmt "noreset %s" i
  | MStep (il, i, vl) ->
    fprintf
      fmt
      "%a := %s%a"
      (pp_comma_list pp_vdecl)
      il
      i
      (pp_print_parenthesized pp_val)
      vl
  | MBranch (g, hl) ->
    fprintf
      fmt
      "@[<v 2>case(%a) {@,%a@]@,}"
      pp_val
      g
      (pp_print_list ~pp_open_box:pp_open_vbox0 pp_branch)
      hl
  | MComment s ->
    pp_print_string fmt ("(*" ^ s ^ "*)")
  | MSpec s ->
    pp_print_string fmt ("@" ^ s));
  (* Annotation *)
  (* let _ = *)
  (* match i.lustre_expr with None -> () | Some e -> fprintf fmt " -- original
     expr: %a" Printers.pp_expr e *)
  (* in *)
  (match i.lustre_eq with
  | None ->
    ()
  | Some eq ->
    fprintf fmt " @[<h>-- original eq: %a@]" Printers.pp_node_eq eq);
  pp_spec m fmt i.instr_spec

and pp_branch m fmt (t, h) =
  fprintf
    fmt
    "@[<v 2>%s:@,%a@]"
    t
    (pp_print_list ~pp_open_box:pp_open_vbox0 (pp_instr m))
    h

let pp_instrs m = pp_print_list ~pp_open_box:pp_open_vbox0 (pp_instr m)

(* merge log: get_node_def was in c0f8 *)
(* Returns the node/machine associated to id in m calls *)
let get_node_def id m =
  try
    let decl, _ = List.assoc id m.mcalls in
    Corelang.node_of_top decl
  with Not_found ->
    (* eprintf "Unable to find node %s in list [%a]@.@?" *)
    (*   id *)
    (* (Utils.fprintf_list ~sep:", " (fun fmt (n,_) -> fprintf fmt "%s" n))
       m.mcalls *)
    (* ; *)
    raise Not_found

(* merge log: machine_vars was in 44686 *)
let machine_vars m =
  m.mstep.step_inputs @ m.mstep.step_locals @ m.mstep.step_outputs @ List.map fst m.mmemory

let pp_step m fmt s =
  fprintf
    fmt
    "@[<v>inputs : %a@ outputs: %a@ locals : %a@ checks : %a@ instrs : @[%a@]@ \
     asserts : @[%a@]@]@ "
    (pp_comma_list Printers.pp_var)
    s.step_inputs
    (pp_comma_list Printers.pp_var)
    s.step_outputs
    (pp_comma_list Printers.pp_var)
    s.step_locals
    (pp_comma_list (fun fmt (_, c) -> pp_val m fmt c))
    s.step_checks
    (pp_instrs m)
    s.step_instrs
    (pp_comma_list (pp_val m))
    s.step_asserts

let pp_static_call fmt (node, args) =
  fprintf fmt "%s<%a>" (node_name node) (pp_comma_list Dimension.pp) args

let pp_instance fmt (o1, o2) = fprintf fmt "(%s, %a)" o1 pp_static_call o2

let pp_memory_pack_base fmt m =
  fprintf
    fmt
    "@[<v 2>MemoryPackBase_%a<SELF> =@ %a@]"
    pp_print_string
    m.mname.node_id
    (PrintSpec.pp_spec m)
    m.mspec.mmemory_pack_base

let pp_memory_pack m fmt mp =
  fprintf
    fmt
    "@[<v 2>MemoryPack_%a<SELF>%a =@ %a@]"
    pp_print_string
    mp.mpname.node_id
    (pp_print_option pp_print_int)
    mp.mpindex
    (PrintSpec.pp_spec m)
    mp.mpformula

let pp_memory_packs m fmt =
  match !Options.spec with
  | Options.SpecNo ->
    pp_print_nothing fmt
  | _ ->
    fprintf fmt "@[<v 2>memory_packs:@ %a@ %a@]"
      pp_memory_pack_base m
      (pp_print_list (pp_memory_pack m))

let pp_transition m fmt t =
  fprintf
    fmt
    "@[<v 2>Transition_%a<SELF>%a%a =@ %a@]"
    pp_print_string
    t.tname.node_id
    (pp_print_option pp_print_int)
    t.tindex
    (pp_print_parenthesized pp_vdecl)
    t.tvars
    (PrintSpec.pp_spec m)
    t.tformula

let pp_transitions m fmt =
  match !Options.spec with
  | Options.SpecNo ->
    pp_print_nothing fmt
  | _ ->
    fprintf fmt "@[<v 2>transitions:@ %a@]" (pp_print_list (pp_transition m))

let pp_mspec m fmt c =
  fprintf
    fmt
    "@[<v>contract: G (H (%a) => %a);]"
    (PrintSpec.pp_spec m)
    c.mc_pre
    (PrintSpec.pp_spec m)
    c.mc_post

let pp_machine fmt m =
  fprintf
    fmt
    "@[<v 2>machine %s@ mem      : %a@ instances: %a@ init     : %a@ const    \
     : %a@ step     :@   @[<v 2>%a@]@ spec     : @[<v>%t@ %a@ @ %a@]@ annot    \
     : @[%a@]@]@ "
    m.mname.node_id
    (pp_comma_list (fun fmt (x, _) -> Printers.pp_var fmt x))
    m.mmemory
    (pp_comma_list pp_instance)
    m.minstances
    (pp_instrs m)
    m.minit
    (pp_instrs m)
    m.mconst
    (pp_step m)
    m.mstep
    (fun fmt ->
      match m.mspec.mnode_spec with
      | None ->
        ()
      | Some (NodeSpec id) ->
        fprintf fmt "cocospec: %s" id
      | Some (Contract spec) ->
        pp_mspec m fmt spec)
    (pp_memory_packs m)
    (snd m.mspec.mmemory_packs)
    (pp_transitions m)
    m.mspec.mtransitions
    (pp_print_list Printers.pp_expr_annot)
    m.mannot

let pp_machines = pp_print_list ~pp_open_box:pp_open_vbox0 pp_machine

let rec is_const_value v =
  match v.value_desc with
  | Cst _ ->
    true
  | Fun (_, args) ->
    Basic_library.is_value_internal_fun v && List.for_all is_const_value args
  | _ ->
    false

(* Returns the declared stateless status and the computed one. *)
let get_stateless_status_node n =
  ( n.node_dec_stateless,
    try Utils.desome n.node_stateless
    with _ ->
      failwith ("stateless status of machine " ^ n.node_id ^ " not computed") )

let get_stateless_status_top_decl td =
  match td.top_decl_desc with
  | Node n ->
    get_stateless_status_node n
  | ImportedNode n ->
    n.nodei_stateless, false
  | _ ->
    true, false

let get_stateless_status m = get_stateless_status_node m.mname

let is_stateless m = m.minstances = [] && m.mmemory = []

(* let is_input m id =
 *   List.exists (fun o -> o.var_id = id.var_id) m.mstep.step_inputs *)

let is_output m id =
  List.exists (fun o -> o.var_id = id.var_id) m.mstep.step_outputs

let get_instr_spec i = i.instr_spec

let mk_val v t = { value_desc = v; value_type = t; value_annot = None }

let vdecl_to_val vd = mk_val (Var vd) vd.var_type

let vdecls_to_vals = List.map vdecl_to_val

let id_to_tag id =
  let typ = (typedef_of_top (Hashtbl.find Corelang.tag_table id)).tydef_id in
  mk_val (Cst (Const_tag id)) (Type_predef.type_const typ)

let mk_conditional ?lustre_eq c t e =
  mkinstr ?lustre_eq (MBranch (c, [ tag_true, t; tag_false, e ]))

let mk_branch ?lustre_eq c br = mkinstr ?lustre_eq (MBranch (c, sort_handlers br))

let mk_branch' ?lustre_eq v = mk_branch ?lustre_eq (vdecl_to_val v)

let mk_assign ?lustre_eq x v = mkinstr ?lustre_eq (MLocalAssign (x, v))

let arrow_machine =
  let state = "_first" in
  let var_state = dummy_var_decl state Type_predef.type_bool in
  let var_input1 = List.nth Arrow.arrow_desc.node_inputs 0 in
  let var_input2 = List.nth Arrow.arrow_desc.node_inputs 1 in
  let var_output = List.nth Arrow.arrow_desc.node_outputs 0 in
  let cst b = mk_val (Cst (const_of_bool b)) Type_predef.type_bool in
  assert (var_input1.var_type = var_input2.var_type);
  let t_arg = var_input1.var_type in
  (* TODO Xavier: c'est bien la bonne def ? Guillaume: Bof preferable de
     reprendre le type des variables non ? *)
  {
    mname = Arrow.arrow_desc;
    mmemory = [ var_state, None ];
    mcalls = [];
    minstances = [];
    minit = [ mkinstr (MStateAssign (var_state, cst true)) ];
    mstatic = [];
    mconst = [];
    mstep =
      {
        step_inputs = Arrow.arrow_desc.node_inputs;
        step_outputs = Arrow.arrow_desc.node_outputs;
        step_locals = [];
        step_checks = [];
        step_instrs =
          [
            mk_conditional
              (mk_val (Var var_state) Type_predef.type_bool)
              (List.map
                 mkinstr
                 [
                   MStateAssign (var_state, cst false);
                   MLocalAssign (var_output, mk_val (Var var_input1) t_arg);
                 ])
              (List.map
                 mkinstr
                 [ MLocalAssign (var_output, mk_val (Var var_input2) t_arg) ]);
          ];
        step_asserts = [];
      };
    mspec = { mnode_spec = None; mtransitions = []; mmemory_packs = -1, []; mmemory_pack_base = True };
    mannot = [];
    msch = None;
    mis_contract = false;
  }

let empty_desc =
  {
    node_id = Arrow.arrow_id;
    node_type = Types.bottom;
    node_clock = Clocks.bottom;
    node_inputs = [];
    node_outputs = [];
    node_locals = [];
    node_gencalls = [];
    node_checks = [];
    node_asserts = [];
    node_stmts = [];
    node_dec_stateless = true;
    node_stateless = Some true;
    node_spec = None;
    node_annot = [];
    node_iscontract = false;
  }

let empty_machine =
  {
    mname = empty_desc;
    mmemory = [];
    mcalls = [];
    minstances = [];
    minit = [];
    mstatic = [];
    mconst = [];
    mstep =
      {
        step_inputs = [];
        step_outputs = [];
        step_locals = [];
        step_checks = [];
        step_instrs = [];
        step_asserts = [];
      };
    mspec = { mnode_spec = None; mtransitions = []; mmemory_packs = -1, []; mmemory_pack_base = True };
    mannot = [];
    msch = None;
    mis_contract = false;
  }

let new_instance =
  let cpt = ref (-1) in
  fun callee tag ->
    let o =
      if Stateless.check_node callee then node_name callee
      else
        Printf.sprintf
          "ni_%d"
          (incr cpt;
           !cpt)
    in
    let o =
      if !Options.ansi && is_generic_node callee then
        Printf.sprintf
          "%s_inst_%d"
          o
          (incr cpt;
           !cpt)
      else o
    in
    o

let get_machine_opt machines name =
  List.fold_left
    (fun res m ->
      match res with
      | Some _ ->
        res
      | None ->
        if m.mname.node_id = name then Some m else None)
    None
    machines

let get_machine machines node_name =
  try desome (get_machine_opt machines node_name)
  with DeSome ->
    eprintf
      "Unable to find machine %s in machines %a@.@?"
      node_name
      (pp_comma_list (fun fmt m -> pp_print_string fmt m.mname.node_id))
      machines;
    assert false

let get_const_assign m id =
  try
    match
      get_instr_desc
        (List.find
           (fun instr ->
             match get_instr_desc instr with
             | MLocalAssign (v, _) ->
               v == id
             | _ ->
               false)
           m.mconst)
    with
    | MLocalAssign (_, e) ->
      e
    | _ ->
      assert false
  with Not_found -> assert false

let value_of_ident loc m id =
  (* is is a state var *)
  try
    let v, _ = List.find (fun (v, _) -> v.var_id = id) m.mmemory in
    mk_val (Var v) v.var_type
  with Not_found -> (
    try
      (* id is a node var *)
      let v = get_node_var id m.mname in
      mk_val (Var v) v.var_type
    with Not_found -> (
      try
        (* id is a constant *)
        let c =
          Corelang.var_decl_of_const
            (const_of_top (Hashtbl.find Corelang.consts_table id))
        in
        mk_val (Var c) c.var_type
      with Not_found ->
        (* id is a tag *)
        let t = Const_tag id in
        mk_val (Cst t) (Typing.type_const loc t)))

(* type of internal fun used in dimension expression *)
let type_of_value_appl f args =
  if List.mem f Basic_library.arith_funs then (List.hd args).value_type
  else Type_predef.type_bool

let rec value_of_dimension m dim =
  match dim.Dimension.dim_desc with
  | Dimension.Dbool b ->
    mk_val
      (Cst (Const_tag (if b then tag_true else tag_false)))
      Type_predef.type_bool
  | Dimension.Dint i ->
    mk_val (Cst (Const_int i)) Type_predef.type_int
  | Dimension.Dident v ->
    value_of_ident dim.Dimension.dim_loc m v
  | Dimension.Dappl (f, args) ->
    let vargs = List.map (value_of_dimension m) args in
    mk_val (Fun (f, vargs)) (type_of_value_appl f vargs)
  | Dimension.Dite (i, t, e) -> (
    match List.map (value_of_dimension m) [ i; t; e ] with
    | [ vi; vt; ve ] ->
      mk_val (Fun ("ite", [ vi; vt; ve ])) vt.value_type
    | _ ->
      assert false)
  | Dimension.Dlink dim' ->
    value_of_dimension m dim'
  | _ ->
    assert false

let rec dimension_of_value value =
  match value.value_desc with
  | Cst (Const_tag t) when t = tag_true ->
    Dimension.mkdim_bool Location.dummy true
  | Cst (Const_tag t) when t = tag_false ->
    Dimension.mkdim_bool Location.dummy false
  | Cst (Const_int i) ->
    Dimension.mkdim_int Location.dummy i
  | Var v ->
    Dimension.mkdim_ident Location.dummy v.var_id
  | Fun (f, args) ->
    Dimension.mkdim_appl Location.dummy f (List.map dimension_of_value args)
  | _ ->
    assert false

let rec join_branches hl1 hl2 =
  match hl1, hl2 with
  | [], _ ->
    hl2
  | _, [] ->
    hl1
  | (t1, h1) :: q1, (t2, h2) :: q2 ->
    if t1 < t2 then (t1, h1) :: join_branches q1 hl2
    else if t1 > t2 then (t2, h2) :: join_branches hl1 q2
    else (t1, List.fold_right join_guards h1 h2) :: join_branches q1 q2

and join_guards inst1 insts2 =
  match get_instr_desc inst1, insts2 with
  | ( MBranch (x1, hl1),
      ({ instr_desc = MBranch (x2, hl2); _ } as inst2) :: insts2 )
    when x1 = x2 ->
    mkinstr
      ~instr_spec:(get_instr_spec inst1 @ get_instr_spec inst2)
      (* TODO on pourrait uniquement concatener les lustres de inst1 et
         hd(inst2) *)
      (MBranch (x1, join_branches (sort_handlers hl1) (sort_handlers hl2)))
    :: insts2
  | _ ->
    inst1 :: insts2

let join_guards_list insts = List.fold_right join_guards insts []
