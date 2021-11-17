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
open Format
open Lustre_types
open Machine_code_types
open C_backend_common
open Corelang
open Spec_types
open Machine_code_common
module Mpfr = Lustrec_mpfr

(**************************************************************************)
(*     Printing spec for c *)

(**************************************************************************)

let pp_acsl_basic_type_desc t_desc =
  if Types.is_bool_type t_desc then
    (* if !Options.cpp then "bool" else "_Bool" *)
    "_Bool"
  else if Types.is_int_type t_desc then
    (* !Options.int_type *)
    if t_desc.tid = -1 then "int" else "integer"
  else if Types.is_real_type t_desc then
    if !Options.mpfr then Mpfr.mpfr_t else !Options.real_type
  else assert false
(* Not a basic C type. Do not handle arrays or pointers *)

let pp_acsl pp fmt = fprintf fmt "@[<v>/*%@ @[<v>%a@]@,*/@]" pp

let pp_acsl_cut pp fmt = fprintf fmt "%a@," (pp_acsl pp)

let pp_acsl_line pp fmt = fprintf fmt "//%@ @[<h>%a@]" pp

let pp_acsl_line' ?(ghost = false) pp fmt x =
  let op = if ghost then "" else "*" in
  let cl = if ghost then "@" else "*" in
  fprintf fmt "/%s%@ @[<h>%a@] %s/" op pp x cl

let pp_acsl_line'_cut pp fmt = fprintf fmt "%a@," (pp_acsl_line' pp)

let pp_requires pp fmt = fprintf fmt "requires %a;" pp

let pp_ensures pp fmt = fprintf fmt "ensures %a;" pp

let pp_terminates pp fmt = fprintf fmt "terminates %a;" pp

let pp_assigns pp =
  pp_comma_list
    ~pp_prologue:(fun fmt () -> pp_print_string fmt "assigns ")
    ~pp_epilogue:pp_print_semicolon'
    pp

let pp_ghost pp fmt = fprintf fmt "ghost %a" pp

let pp_assert pp fmt = fprintf fmt "assert %a;" pp

let pp_loop_invariant pp fmt = fprintf fmt "loop invariant %a;" pp

let pp_mem_valid pp_var fmt (name, var) =
  fprintf fmt "%s_valid(%a)" name pp_var var

let pp_mem_valid' = pp_mem_valid pp_print_string

let pp_ref pp fmt = fprintf fmt "&%a" pp

let pp_ref' = pp_ref pp_print_string

let pp_indirect pp_ptr pp_field fmt (ptr, field) =
  fprintf fmt "%a->%a" pp_ptr ptr pp_field field

let pp_indirect' = pp_indirect pp_print_string pp_print_string

let pp_access pp_stru pp_field fmt (stru, field) =
  fprintf fmt "%a.%a" pp_stru stru pp_field field

let pp_access' = pp_access pp_print_string pp_print_string

let pp_var_decl fmt v = pp_print_string fmt v.var_id

let pp_true fmt () = pp_print_string fmt "\\true"

let pp_cast pp_ty pp fmt (ty, x) = fprintf fmt "(%a) %a" pp_ty ty pp x

let pp_bool_cast pp fmt x = pp_cast pp_print_string pp fmt ("_Bool", x)

let pp_double_cast pp fmt x = pp_cast pp_print_string pp fmt ("double", x)

let pp_int_cast pp fmt x = pp_cast pp_print_string pp fmt ("int", x)

let pp_true_c_bool fmt () = pp_bool_cast pp_print_string fmt "1"

let pp_false fmt () = pp_print_string fmt "\\false"

let pp_nothing fmt () = pp_print_string fmt "\\nothing"

let pp_null fmt () = pp_print_string fmt "\\null"

let pp_stdout fmt () = pp_print_string fmt "stdout"

let pp_at pp_v fmt (v, l) = fprintf fmt "\\at(%a, %s)" pp_v v l

let pp_at_pre pp_v fmt v = pp_at pp_v fmt (v, "Pre")

let find_machine f = List.find (fun m -> m.mname.node_id = f)

let instances machines m =
  let rec aux m =
    List.(
      fold_left
        (fun insts (inst, (td, _)) ->
          let mems, insts' =
            try
              let m' = find_machine (node_name td) machines in
              m'.mmemory, aux m'
            with Not_found ->
              if Arrow.td_is_arrow td then arrow_machine.mmemory, [ [] ]
              else assert false
          in
          insts @ map (cons (inst, (td, mems))) insts')
        [ [] ]
        m.minstances)
  in
  match aux m with [] :: l -> l | l -> l

let pp_instance ?(indirect = true) ?pp_epilogue fmt =
  pp_print_list
    ~pp_sep:(fun fmt () -> pp_print_string fmt (if indirect then "->" else "."))
    ?pp_epilogue
    (fun fmt (i, _) -> pp_print_string fmt i)
    fmt

let pp_reg ?(indirect = true) self fmt paths =
  fprintf
    fmt
    "%s->%a%s"
    self
    (pp_instance ~indirect ~pp_epilogue:(fun fmt () ->
         pp_print_string fmt (if indirect then "->" else ".")))
    paths
    "_reg"

let pp_separated pp_self pp_mem pp_ptr fmt (self, mem, paths, ptrs) =
  fprintf
    fmt
    "\\separated(@[<v>%a, %a%a%a@])"
    pp_self
    self
    pp_mem
    mem
    (pp_comma_list ~pp_prologue:pp_print_comma (fun fmt path ->
         pp_indirect pp_print_string pp_instance fmt (self, path)))
    paths
    (pp_comma_list ~pp_prologue:pp_print_comma pp_ptr)
    ptrs

let pp_separated' self mem fmt (paths, ptrs) =
  pp_separated
    pp_print_string
    pp_print_string
    pp_var_decl
    fmt
    (self, mem, paths, ptrs)

let pp_separated'' =
  pp_comma_list
    ~pp_prologue:(fun fmt () -> pp_print_string fmt "\\separated(")
    ~pp_epilogue:pp_print_cpar
    pp_var_decl

let pp_forall pp_l pp_r fmt (l, r) =
  fprintf fmt "@[<v 2>\\forall @[<hov>%a@];@,%a@]" pp_l l pp_r r

let pp_exists pp_l pp_r fmt (l, r) =
  fprintf fmt "@[<v 2>\\exists %a;@,%a@]" pp_l l pp_r r

let pp_equal pp_l pp_r fmt (l, r) = fprintf fmt "%a == %a" pp_l l pp_r r

let pp_gequal pp_l pp_r fmt (l, r) = fprintf fmt "%a >= %a" pp_l l pp_r r

let pp_implies pp_l pp_r fmt (l, r) =
  fprintf fmt "@[<v>%a ==>@ %a@]" pp_l l pp_r r

let pp_and pp_l pp_r fmt (l, r) = fprintf fmt "@[<v>%a @ && %a@]" pp_l l pp_r r

let pp_and_l pp_v fmt =
  pp_print_list
    ~pp_open_box:pp_open_vbox0
    ~pp_sep:(fun fmt () -> fprintf fmt "@,&& ")
    ~pp_nil:pp_true
    pp_v
    fmt

let pp_or pp_l pp_r fmt (l, r) = fprintf fmt "@[<v>%a @ || %a@]" pp_l l pp_r r

let pp_or_l pp_v fmt =
  pp_print_list
    ~pp_open_box:pp_open_vbox0
    ~pp_sep:(fun fmt () -> fprintf fmt "@,|| ")
    pp_v
    fmt

let pp_not pp fmt = fprintf fmt "!%a" pp

let pp_valid pp = pp_and_l (fun fmt x -> fprintf fmt "\\valid(%a)" pp x)

let pp_valid_read pp fmt = fprintf fmt "\\valid_read(%a)" pp

let pp_old pp fmt = fprintf fmt "\\old(%a)" pp

let pp_ite pp_c pp_t pp_f fmt (c, t, f) =
  fprintf fmt "(%a @[<hov>? %a@ : %a)@]" pp_c c pp_t t pp_f f

let pp_paren pp fmt v = fprintf fmt "(%a)" pp v

let pp_initialization pp_mem fmt (name, mem) =
  fprintf fmt "%s_initialization(%a)" name pp_mem mem

let pp_init pp_mem fmt (name, mem) = fprintf fmt "%s_init(%a)" name pp_mem mem

let pp_initialization' = pp_initialization pp_print_string

let pp_local m =
  pp_c_decl_local_var ~pp_c_basic_type_desc:pp_acsl_basic_type_desc m

let pp_locals m =
  pp_comma_list ~pp_open_box:(fun fmt () -> pp_open_hovbox fmt 0) (pp_local m)

let pp_ptr_decl fmt v = pp_ptr fmt v.var_id

let pp_basic_assign_spec ?(pp_op = pp_equal) pp_l pp_r fmt (typ, var_name, value) =
  if Types.is_real_type typ && !Options.mpfr then assert false
    (* Mpfr.pp_inject_assign pp_var fmt (var_name, value) *)
  else pp_op pp_l pp_r fmt (var_name, value)

let pp_assign_spec ?pp_op m self_l pp_var_l indirect_l self_r pp_var_r
    indirect_r fmt (var_type, var_name, value) =
  let depth = expansion_depth value in
  let loop_vars = mk_loop_variables m var_type depth in
  let reordered_loop_vars = reorder_loop_variables loop_vars in
  let aux typ fmt vars =
    match vars with
    | [] ->
      pp_basic_assign_spec
        ?pp_op
        (pp_value_suffix
           ~indirect:indirect_l
           m
           self_l
           var_type
           loop_vars
           pp_var_l)
        (pp_value_suffix
           ~indirect:indirect_r
           m
           self_r
           var_type
           loop_vars
           pp_var_r)
        fmt
        (typ, var_name, value)
    | (_d, LVar _i) :: _q ->
      assert false
    (* let typ' = Types.array_element_type typ in
     * fprintf fmt "@[<v 2>{@,int %s;@,for(%s=0;%s<%a;%s++)@,%a @]@,}"
     *   i i i pp_c_dimension d i
     *   (aux typ') q *)
    | (_d, LInt _r) :: _q ->
      assert false
    (* let typ' = Types.array_element_type typ in
     * let szl = Utils.enumerate (Dimension.size_const_dimension d) in
     * fprintf fmt "@[<v 2>{@,%a@]@,}"
     *   (pp_print_list (fun fmt i -> r := i; aux typ' fmt q)) szl *)
    | _ ->
      assert false
  in
  reset_loop_counter ();
  aux var_type fmt reordered_loop_vars

let pp_memory_pack_aux ?i pp_mem pp_self fmt (name, mem, self) =
  fprintf
    fmt
    "%s_pack%a(@[<hov>%a,@ %a@])"
    name
    (pp_print_option pp_print_int)
    i
    pp_mem
    mem
    pp_self
    self

let pp_memory_pack pp_mem pp_self fmt (mp, mem, self) =
  pp_memory_pack_aux
    ?i:mp.mpindex
    pp_mem
    pp_self
    fmt
    (mp.mpname.node_id, mem, self)

let pp_transition_aux ?i stateless pp_mem_in pp_mem_out pp_var fmt
    (name, vars, mem_in, mem_out) =
  fprintf
    fmt
    "%s_transition%a(@[<hov>%t%a%t@])"
    name
    (pp_print_option pp_print_int)
    i
    (fun fmt -> if not stateless then pp_mem_in fmt mem_in)
    (pp_comma_list
       ~pp_prologue:(fun fmt () -> if not stateless then pp_print_comma fmt ())
       pp_var)
    vars
    (fun fmt -> if not stateless then fprintf fmt ",@ %a" pp_mem_out mem_out)

let pp_transition stateless pp_mem_in pp_mem_out pp_var fmt (t, mem_in, mem_out)
    =
  pp_transition_aux
    ?i:t.tindex
    stateless
    pp_mem_in
    pp_mem_out
    pp_var
    fmt
    (t.tname.node_id, t.tvars, mem_in, mem_out)

let pp_transition_aux' ?i m =
  let stateless = fst (get_stateless_status m) in
  pp_transition_aux ?i stateless pp_print_string pp_print_string (fun fmt v ->
      (if is_output m v then pp_ptr_decl else pp_var_decl) fmt v)

let pp_reset_cleared pp_mem_in pp_mem_out fmt (name, mem_in, mem_out) =
  fprintf
    fmt
    "%s_reset_cleared(@[<hov>%a,@ %a@])"
    name
    pp_mem_in
    mem_in
    pp_mem_out
    mem_out

let pp_reset_cleared' = pp_reset_cleared pp_print_string pp_print_string

let pp_functional_update mems insts fmt mem =
  let rec aux fmt = function
    | [] ->
      pp_print_string fmt mem
    | (x, is_mem) :: fields ->
      fprintf
        fmt
        "{ @[<hov>%a@ \\with .%s%s = %s@] }"
        aux
        fields
        (if is_mem then "_reg." else "")
        x
        x
  in
  aux
    fmt
    (List.map (fun (x, _) -> x, false) (Utils.IMap.bindings insts)
    @ List.map (fun x -> x, true) (Utils.ISet.elements mems))

module PrintSpec = struct
  type mode =
    | MemoryPackMode
    | TransitionMode
    | TransitionFootprintMode
    | ResetIn
    | ResetOut
    | InstrMode of ident

  let pp_reg mem fmt = function
    | ResetFlag ->
      fprintf fmt "%s.%s" mem reset_flag_name
    | StateVar x ->
      fprintf fmt "%s.%a" mem pp_var_decl x

  let not_var v = match v.value_desc with Var _ -> false | _ -> true

  let pp_expr ?(test_output = false) m mem fmt = function
    | Val v ->
      let pp = pp_c_val ~indirect:false m mem (pp_c_var_read ~test_output m) in
      (if not_var v then
       if Types.is_bool_type v.value_type then pp_bool_cast pp
       else if Types.is_real_type v.value_type then pp_double_cast pp
       else if Types.is_int_type v.value_type then pp_int_cast pp
       else pp
      else pp)
        fmt
        v
    | Tag (t, _) ->
      pp_print_string fmt t
    | Var v ->
      pp_var_decl fmt v
    | Memory r ->
      pp_reg mem fmt r

  let pp_predicate mode m mem_in mem_in' mem_out mem_out' fmt p =
    let test_output, mem_update =
      match mode with
      | InstrMode _ ->
        true, false
      | TransitionFootprintMode ->
        false, true
      | _ ->
        false, false
    in
    let pp_expr test_output fmt e = pp_expr ~test_output m mem_out fmt e in
    match p with
    | Transition (stateless, f, inst, i, vars, r, mems, insts) ->
      let pp_mem_in, pp_mem_out =
        match inst with
        | None ->
          ( pp_print_string,
            if mem_update then pp_functional_update mems insts
            else pp_print_string )
        | Some inst ->
          ( (fun fmt mem_in ->
              if r then pp_print_string fmt mem_in
              else pp_access' fmt (mem_in, inst)),
            fun fmt mem_out -> pp_access' fmt (mem_out, inst) )
      in
      pp_transition_aux
        ?i
        stateless
        pp_mem_in
        pp_mem_out
        (pp_expr test_output)
        fmt
        (f, vars, mem_in', mem_out')
    | Reset (_f, inst, r) ->
      pp_ite
        (pp_c_val m mem_in (pp_c_var_read m))
        (pp_equal (pp_reset_flag' ~indirect:false) pp_print_int)
        (pp_equal pp_print_string pp_access')
        fmt
        (r, (mem_out, 1), (mem_out, (mem_in, inst)))
    | MemoryPack (f, inst, i) ->
      let pp_mem, pp_self =
        match inst with
        | None ->
          pp_print_string, pp_print_string
        | Some inst ->
          ( (fun fmt mem -> pp_access' fmt (mem, inst)),
            fun fmt self -> pp_indirect' fmt (self, inst) )
      in
      pp_memory_pack_aux ?i pp_mem pp_self fmt (f, mem_out, mem_in)
    | ResetCleared f ->
      pp_reset_cleared' fmt (f, mem_in, mem_out)
    (* fprintf fmt "ResetCleared_%a" pp_print_string f *)
    | Initialization ->
      ()
    | GhostAssign (v1, v2) ->
      pp_ghost (pp_assign m mem_in (pp_c_var_read m)) fmt (v1, vdecl_to_val v2)

  let reset_flag = dummy_var_decl "_reset" Type_predef.type_bool

  let val_of_expr = function
    | Val v ->
      v
    | Tag (t, _) ->
      id_to_tag t
    | Var v ->
      vdecl_to_val v
    | Memory (StateVar v) ->
      vdecl_to_val v
    | Memory ResetFlag ->
      vdecl_to_val reset_flag

  let find_arrow loc m =
    match
      List.find_opt (fun (_, (td, _)) -> Arrow.td_is_arrow td) m.minstances
    with
    | Some (f, _) ->
      Some f
    | None ->
      Error.pp_warning loc (fun fmt ->
          pp_print_string
            fmt
            "Generating stateful spec for uninitialized state variables.");
      None

  let rec has_memory_val m v =
    let has_mem = has_memory_val m in
    match v.value_desc with
    | Var v ->
      is_memory m v
    | Array vl | Fun (_, vl) ->
      List.exists has_mem vl
    | Access (t, i) | Power (t, i) ->
      has_mem t || has_mem i
    | _ ->
      false

  let has_memory m = function Val v -> has_memory_val m v | _ -> false

  let pp_spec mode m fmt f =
    let rec pp_spec mode fmt f =
      let mem_in, mem_in', indirect_r, mem_out, mem_out', indirect_l =
        let self = mk_self m in
        let mem = mk_mem m in
        let mem_in = mk_mem_in m in
        let mem_out = mk_mem_out m in
        let mem_reset = mk_mem_reset m in
        match mode with
        | MemoryPackMode ->
          self, self, true, mem, mem, false
        | TransitionMode ->
          mem_in, mem_in, false, mem_out, mem_out, false
        | TransitionFootprintMode ->
          mem_in, mem_in, false, mem_out, mem_out, false
        | ResetIn ->
          mem_reset, mem_reset, false, mem_out, mem_out, false
        | ResetOut ->
          mem_in, mem_in, false, mem_reset, mem_reset, false
        | InstrMode self ->
          let mem = "(*" ^ mem ^ ")" in
          self, mem_reset, false, mem, mem, false
      in
      let pp_expr fmt e = pp_expr m mem_out fmt e in
      let pp_spec' = pp_spec mode in
      match f with
      | True ->
        pp_true fmt ()
      | False ->
        pp_false fmt ()
      | Equal (a, b) ->
        let pp_eq fmt () =
          pp_assign_spec
            m
            mem_out
            (pp_c_var_read ~test_output:false m)
            indirect_l
            mem_in
            (pp_c_var_read ~test_output:false m)
            indirect_r
            fmt
            (Spec_common.type_of_value a, val_of_expr a, val_of_expr b)
        in
        if has_memory m b then
          let inst = find_arrow Location.dummy m in
          pp_print_option
            ~none:pp_eq
            (fun fmt inst ->
              pp_paren
                (pp_implies (pp_not (pp_initialization pp_access')) pp_eq)
                fmt
                ((Arrow.arrow_id, (mem_in, inst)), ()))
            fmt
            inst
        else pp_eq fmt ()
      | GEqual (a, b) ->
        pp_assign_spec
          ~pp_op:pp_gequal
          m
          mem_out
          (pp_c_var_read ~test_output:false m)
          indirect_l
          mem_in
          (pp_c_var_read ~test_output:false m)
          indirect_r
          fmt
          (Spec_common.type_of_value a, val_of_expr a, val_of_expr b)
      | And fs ->
        pp_and_l pp_spec' fmt fs
      | Or fs ->
        pp_or_l pp_spec' fmt fs
      | Imply (a, b) ->
        pp_paren (pp_implies pp_spec' pp_spec') fmt (a, b)
      | Exists ([x], a) ->
        pp_exists (pp_local m) pp_spec' fmt (x, a)
      | Exists (xs, a) ->
        pp_spec' fmt (List.fold_left (fun spec x -> Exists ([x], spec)) a xs)
      | Forall (xs, a) ->
        pp_forall (pp_locals m) pp_spec' fmt (xs, a)
      | Ternary (e, a, b) ->
        pp_ite pp_expr pp_spec' pp_spec' fmt (e, a, b)
      | Predicate p ->
        pp_predicate mode m mem_in mem_in' mem_out mem_out' fmt p
      | StateVarPack ResetFlag ->
        let r = vdecl_to_val reset_flag in
        pp_assign_spec
          m
          mem_out
          (pp_c_var_read ~test_output:false m)
          indirect_l
          mem_in
          (pp_c_var_read ~test_output:false m)
          indirect_r
          fmt
          (Type_predef.type_bool, r, r)
      | StateVarPack (StateVar v) ->
        let v' = vdecl_to_val v in
        let pp_eq fmt () =
          pp_assign_spec
            m
            mem_out
            (pp_c_var_read ~test_output:false m)
            indirect_l
            mem_in
            (pp_c_var_read ~test_output:false m)
            indirect_r
            fmt
            (v.var_type, v', v')
        in
        let inst = find_arrow Location.dummy m in
        pp_print_option
          ~none:pp_eq
          (fun fmt inst ->
            pp_paren
              (pp_implies (pp_not (pp_initialization pp_access')) pp_eq)
              fmt
              ((Arrow.arrow_id, (mem_out, inst)), ()))
          fmt
          inst
      | ExistsMem (f, rc, tr) ->
        pp_exists
          (pp_machine_decl' ~ghost:true)
          (pp_and (pp_spec ResetOut) (pp_spec ResetIn))
          fmt
          ((f, mk_mem_reset m), (rc, tr))
      | Value v ->
        pp_c_val m mem_in (pp_c_var_read ~test_output:true m) fmt v
    in

    pp_spec mode fmt (Spec_common.red f)
end

let pp_predicate pp_l pp_r fmt (l, r) =
  fprintf fmt "@[<v 2>predicate %a =@,%a;@]" pp_l l pp_r r

let pp_lemma pp_l pp_r fmt (l, r) =
  fprintf fmt "@[<v 2>lemma %a:@,%a;@]" pp_l l pp_r r

let pp_axiomatic pp_l pp_r fmt (l, r) =
  fprintf fmt "@[<v 2>axiomatic %a {@,%a@]@;}" pp_l l pp_r r

let pp_axiom pp_l pp_r fmt (l, r) =
  fprintf fmt "@[<v 2>axiom %a:@,%a;@]" pp_l l pp_r r

let pp_mem_valid_def fmt m =
  if not (fst (get_stateless_status m) || m.mis_contract) then
    let name = m.mname.node_id in
    let self = mk_self m in
    pp_acsl
      (pp_predicate
         (pp_mem_valid (pp_machine_decl pp_ptr))
         (pp_and
            (pp_and_l (fun fmt (inst, (td, _)) ->
                 if Arrow.td_is_arrow td then
                   pp_valid pp_indirect' fmt [ self, inst ]
                 else pp_mem_valid pp_indirect' fmt (node_name td, (self, inst))))
            (pp_valid pp_print_string)))
      fmt
      ((name, (name, self)), (m.minstances, [ self ]))

let pp_memory_pack_def m fmt mp =
  if not (fst (get_stateless_status m) || m.mis_contract) then
    let name = mp.mpname.node_id in
    let self = mk_self m in
    let mem = mk_mem m in
    pp_acsl_cut
      (pp_predicate
         (pp_memory_pack
            (pp_machine_decl' ~ghost:true)
            (pp_machine_decl pp_ptr))
         (PrintSpec.pp_spec MemoryPackMode m))
      fmt
      ((mp, (name, mem), (name, self)), mp.mpformula)

let pp_machine_ghost_struct fmt m =
  pp_acsl (pp_ghost (pp_machine_struct ~ghost:true)) fmt m

let pp_memory_pack_defs fmt m =
  if not (fst (get_stateless_status m)) then
    fprintf
      fmt
      "%a@,%a"
      pp_machine_ghost_struct
      m
      (pp_print_list
         ~pp_sep:pp_print_nothing
         ~pp_epilogue:pp_print_cut
         ~pp_open_box:pp_open_vbox0
         (pp_memory_pack_def m))
      (snd m.mspec.mmemory_packs)

let pp_transition_def m fmt t =
  let name = t.tname.node_id in
  let mem_in = mk_mem_in m in
  let mem_out = mk_mem_out m in
  let stateless = fst (get_stateless_status m) in
  pp_acsl
    (pp_predicate
       (pp_transition
          stateless
          (pp_machine_decl' ~ghost:true)
          (pp_machine_decl' ~ghost:true)
          (pp_local m))
       (PrintSpec.pp_spec TransitionMode m))
    fmt
    ((t, (name, mem_in), (name, mem_out)), t.tformula)

let pp_transition_defs fmt m =
  pp_print_list
    ~pp_epilogue:pp_print_cut
    ~pp_open_box:pp_open_vbox0
    (pp_transition_def m)
    fmt
    m.mspec.mtransitions

let pp_transition_footprint fmt t =
  fprintf
    fmt
    "%s_transition%a_footprint"
    t.tname.node_id
    (pp_print_option pp_print_int)
    t.tindex

let pp_transition_footprint_lemma m fmt t =
  let name = t.tname.node_id in
  let mem_in = mk_mem_in m in
  let mem_out = mk_mem_out m in
  let stateless = fst (get_stateless_status m) in
  let mems =
    ISet.(
      diff (of_list (List.map (fun v -> v.var_id) m.mmemory)) t.tmem_footprint)
  in
  let insts =
    IMap.(
      diff
        (of_list (List.map (fun (x, (td, _)) -> x, node_name td) m.minstances))
        t.tinst_footprint)
  in
  let memories =
    List.map
      (fun v -> { v with var_type = { v.var_type with tid = -1 } })
      (List.filter (fun v -> ISet.mem v.var_id mems) m.mmemory)
  in
  let mems_empty = ISet.is_empty mems in
  let insts_empty = IMap.is_empty insts in
  let instances = List.map (fun (i, f) -> f, i) (IMap.bindings insts) in
  let tr ?mems ?insts () =
    Spec_common.mk_transition
      ?mems
      ?insts
      ?i:t.tindex
      stateless
      name
      (vdecls_to_vals t.tvars)
  in
  if not ((mems_empty && insts_empty) || m.mis_contract) then
    pp_acsl_cut
      (pp_lemma
         pp_transition_footprint
         (pp_forall
            (pp_machine_decl ~ghost:true (pp_comma_list pp_print_string))
            ((if insts_empty then fun pp fmt (_, x) -> pp fmt x
             else pp_forall (pp_comma_list (pp_machine_decl' ~ghost:true)))
               ((if mems_empty then fun pp fmt (_, x) -> pp fmt x
                else pp_forall (pp_locals m))
                  (PrintSpec.pp_spec TransitionFootprintMode m)))))
      fmt
      ( t,
        ( (m.mname.node_id, [ mem_in; mem_out ]),
          ( instances,
            (memories, Forall (t.tvars, Imply (tr (), tr ~mems ~insts ()))) ) )
      )

let pp_transition_footprint_lemmas fmt m =
  pp_print_list
    ~pp_epilogue:pp_print_cut
    ~pp_open_box:pp_open_vbox0
    ~pp_sep:pp_print_nothing
    (pp_transition_footprint_lemma m)
    fmt
    (List.filter
       (fun t -> match t.tindex with Some i when i > 0 -> true | _ -> false)
       m.mspec.mtransitions)

let pp_initialization_def fmt m =
  if not (fst (get_stateless_status m)) then
    let name = m.mname.node_id in
    let mem_in = mk_mem_in m in
    pp_acsl
      (pp_predicate
         (pp_initialization (pp_machine_decl' ~ghost:true))
         (pp_and_l (fun fmt (i, (td, _)) ->
              if Arrow.td_is_arrow td then
                pp_initialization pp_access' fmt (node_name td, (mem_in, i))
              else
                pp_equal
                  (pp_reset_flag ~indirect:false pp_access')
                  pp_print_int
                  fmt
                  ((mem_in, i), 1))))
      fmt
      ((name, (name, mem_in)), m.minstances)

let pp_reset_cleared_def fmt m =
  if not (fst (get_stateless_status m)) then
    let name = m.mname.node_id in
    let mem_in = mk_mem_in m in
    let mem_out = mk_mem_out m in
    pp_acsl
      (pp_predicate
         (pp_reset_cleared
            (pp_machine_decl' ~ghost:true)
            (pp_machine_decl' ~ghost:true))
         (pp_ite
            (pp_reset_flag' ~indirect:false)
            (pp_and
               (pp_equal (pp_reset_flag' ~indirect:false) pp_print_int)
               pp_initialization')
            (pp_equal pp_print_string pp_print_string)))
      fmt
      ( (name, (name, mem_in), (name, mem_out)),
        (mem_in, ((mem_out, 0), (name, mem_out)), (mem_out, mem_in)) )

let pp_register_chain ?(indirect = true) ptr =
  pp_print_list
    ~pp_prologue:(fun fmt () -> fprintf fmt "%s->" ptr)
    ~pp_epilogue:(fun fmt () ->
      fprintf fmt "%s_reg._first" (if indirect then "->" else "."))
    ~pp_sep:(fun fmt () -> pp_print_string fmt (if indirect then "->" else "."))
    (fun fmt (i, _) -> pp_print_string fmt i)

let pp_reset_flag_chain ?(indirect = true) ptr fmt mems =
  pp_print_list
    ~pp_prologue:(fun fmt () -> fprintf fmt "%s->" ptr)
    ~pp_epilogue:(fun fmt () -> pp_reset_flag' ~indirect fmt "")
    ~pp_sep:(fun fmt () -> pp_print_string fmt (if indirect then "->" else "."))
    (fun fmt (i, _) -> pp_print_string fmt i)
    fmt
    mems

let pp_arrow_reset_ghost mem fmt inst =
  fprintf fmt "%s_reset_ghost(%a)" Arrow.arrow_id pp_indirect' (mem, inst)

module GhostProto : MODIFIERS_GHOST_PROTO = struct
  let pp_ghost_parameters ?(cut = true) fmt vs =
    fprintf
      fmt
      "%a%a"
      (if cut then pp_print_cut else pp_print_nothing)
      ()
      (pp_acsl_line'
         (pp_ghost (pp_print_parenthesized (fun fmt (x, pp) -> pp fmt x))))
      vs
end

module HdrMod = struct
  module GhostProto = GhostProto

  let pp_machine_decl_prefix _ _ = ()

  let pp_import_arrow fmt () =
    fprintf
      fmt
      "#include \"%s/arrow_spec.h%s\""
      (Arrow.arrow_top_decl ()).top_decl_owner
      (if !Options.cpp then "pp" else "")

  let pp_predicates fmt machines =
    let pp_preds comment pp =
      pp_print_list
        ~pp_open_box:pp_open_vbox0
        ~pp_prologue:(pp_print_endcut comment)
        pp
        ~pp_epilogue:pp_print_cutcut
    in
    fprintf
      fmt
      "%a%a"
      (pp_preds "/* ACSL `valid` predicates */" pp_mem_valid_def)
      machines
      (pp_preds "/* ACSL `memory pack` simulations */" pp_memory_pack_defs)
      machines

  let pp_machine_alloc_decl fmt m =
    pp_machine_decl_prefix fmt m;
    if not (fst (get_stateless_status m)) then
      if !Options.static_mem then
        (* Static allocation *)
        let macro = m, mk_attribute m, mk_instance m in
        fprintf
          fmt
          "%a@,%a@,%a"
          (pp_static_declare_macro ~ghost:true)
          macro
          (pp_static_link_macro ~ghost:true)
          macro
          (pp_static_alloc_macro ~ghost:true)
          macro
      else
        (* Dynamic allocation *)
        (* TODO: handle dynamic alloc *)
        assert false
  (* fprintf fmt "extern %a;@,extern %a" pp_alloc_prototype
   *   (m.mname.node_id, m.mstatic)
   *   pp_dealloc_prototype m.mname.node_id *)
end

module SrcMod = struct
  module GhostProto = GhostProto

  let pp_predicates fmt machines =
    let pp_preds comment pp =
      pp_print_list
        ~pp_open_box:pp_open_vbox0
        ~pp_prologue:(pp_print_endcut comment)
        pp
        ~pp_epilogue:pp_print_cutcut
    in
    fprintf
      fmt
      "%a%a%a%a%a%a"
      (pp_preds "/* ACSL `valid` predicates */" pp_mem_valid_def)
      machines
      (pp_preds "/* ACSL `memory pack` simulations */" pp_memory_pack_defs)
      machines
      (pp_preds "/* ACSL initialization annotations */" pp_initialization_def)
      machines
      (pp_preds "/* ACSL reset cleared annotations */" pp_reset_cleared_def)
      machines
      (pp_preds "/* ACSL transition annotations */" pp_transition_defs)
      machines
      (pp_preds
         "/* ACSL transition memory footprints lemmas */"
         pp_transition_footprint_lemmas)
      machines

  let pp_clear_reset_spec fmt self mem m =
    let name = m.mname.node_id in
    let arws, narws =
      List.partition (fun (_, (td, _)) -> Arrow.td_is_arrow td) m.minstances
    in
    let mk_insts = List.map (fun x -> [ x ]) in
    pp_acsl_cut
      (fun fmt () ->
        fprintf
          fmt
          "%a@,\
           %a@,\
           %a@,\
           %a@,\
           %a@,\
           %a@,\
           %a@,\
           %a@,\
           %a@,\
           %a@,\
           %a"
          (pp_requires pp_mem_valid')
          (name, self)
          (pp_requires (pp_separated' self mem))
          (mk_insts m.minstances, [])
          (pp_requires (pp_memory_pack_aux pp_ptr pp_print_string))
          (name, mem, self)
          (pp_ensures
             (pp_memory_pack_aux
                ~i:(fst m.mspec.mmemory_packs)
                pp_ptr
                pp_print_string))
          (name, mem, self)
          (pp_ensures
             (pp_reset_cleared (pp_old pp_ptr) pp_ptr))
          (name, mem, mem)
          (pp_assigns pp_reset_flag')
          [ self ]
          (pp_assigns (pp_register_chain self))
          (mk_insts arws)
          (pp_assigns (pp_reset_flag_chain self))
          (mk_insts narws)
          (pp_assigns pp_reset_flag')
          [ mem ]
          (pp_assigns (pp_register_chain ~indirect:false mem))
          (mk_insts arws)
          (pp_assigns (pp_reset_flag_chain ~indirect:false mem))
          (mk_insts narws))
      fmt
      ()

  let pp_set_reset_spec fmt self mem m =
    let name = m.mname.node_id in
    pp_acsl_cut
      (fun fmt () ->
        fprintf
          fmt
          "%a@,%a@,%a"
          (pp_ensures (pp_memory_pack_aux pp_ptr pp_print_string))
          (name, mem, self)
          (pp_ensures (pp_equal pp_reset_flag' pp_print_int))
          (mem, 1)
          (pp_assigns pp_reset_flag')
          [ self; mem ])
      fmt
      ()

  let spec_from_contract c = Spec_common.red (Imply (c.mc_pre, c.mc_post))

  let pp_contract m fmt c =
    PrintSpec.pp_spec PrintSpec.TransitionMode m fmt (spec_from_contract c)

  let contract_of machines m =
    match m.mspec.mnode_spec with
    | Some spec -> (
      match spec with
      | Contract c ->
        Some c, None
      | NodeSpec f -> (
        let m_f = find_machine f machines in
        match m_f.mspec.mnode_spec with
        | Some (Contract c) ->
          Some c, Some m_f
        | _ ->
          None, None))
    | None ->
      None, None

  let pp_init_def fmt m =
    let name = m.mname.node_id in
    let mem = mk_mem m in
    pp_predicate
      (pp_init (pp_machine_decl' ~ghost:true))
      (pp_and pp_initialization' (pp_reset_flag' ~indirect:false))
      fmt
      ((name, (name, mem)), ((name, mem), mem))

  let rename n x = sprintf "%s_%d" x n

  let rename_var_decl n vd = { vd with var_id = rename n vd.var_id }

  let rec rename_value n v =
    {
      v with
      value_desc =
        (match v.value_desc with
        | Machine_code_types.Var v ->
          Machine_code_types.Var (rename_var_decl n v)
        | Fun (f, vs) ->
          Fun (f, List.map (rename_value n) vs)
        | Array vs ->
          Array (List.map (rename_value n) vs)
        | Access (v1, v2) ->
          Access (rename_value n v1, rename_value n v2)
        | Power (v1, v2) ->
          Power (rename_value n v1, rename_value n v2)
        | v ->
          v);
    }

  let rename_expression n = function
    | Val v ->
      Val (rename_value n v)
    | Var v ->
      Var (rename_var_decl n v)
    | e ->
      e

  let rename_predicate n = function
    | Transition (s, f, inst, i, es, r, mf, mif) ->
      Transition (s, f, inst, i, List.map (rename_expression n) es, r, mf, mif)
    | p ->
      p

  let rec rename_formula n = function
    | Equal (e1, e2) ->
      Equal (rename_expression n e1, rename_expression n e2)
    | And fs ->
      And (List.map (rename_formula n) fs)
    | Or fs ->
      Or (List.map (rename_formula n) fs)
    | Imply (f1, f2) ->
      Imply (rename_formula n f1, rename_formula n f2)
    | Exists (xs, f) ->
      Exists (List.map (rename_var_decl n) xs, rename_formula n f)
    | Forall (xs, f) ->
      Forall (List.map (rename_var_decl n) xs, rename_formula n f)
    | Ternary (e, t, f) ->
      Ternary (rename_expression n e, rename_formula n t, rename_formula n f)
    | Predicate p ->
      Predicate (rename_predicate n p)
    | ExistsMem (x, f1, f2) ->
      ExistsMem (rename n x, rename_formula n f1, rename_formula n f2)
    | Value v ->
      Value (rename_value n v)
    | f ->
      f

  let rename_contract n c =
    {
      c with
      mc_pre = rename_formula n c.mc_pre;
      mc_post = rename_formula n c.mc_post;
    }

  let but_last l = List.(rev (tl (rev l)))

  let pp_k_induction_case case m pp_mem_in pp_mem_out pp_vars fmt
      (n, mem_in, mem_out) =
    let name = m.mname.node_id in
    let inputs = m.mstep.step_inputs in
    let outputs = m.mstep.step_outputs in
    fprintf
      fmt
      "%s_%s_%d(@[<hov>%a,@;%a,@;%a@])"
      name
      case
      n
      pp_mem_in
      mem_in
      pp_vars
      (inputs @ outputs)
      pp_mem_out
      mem_out

  let pp_k_induction_base_case m = pp_k_induction_case "base" m

  let pp_k_induction_inductive_case m = pp_k_induction_case "inductive" m

  let pp_base_cases m fmt (c, m_c, k) =
    let name = m.mname.node_id in
    let name_c = m_c.mname.node_id in
    let mem = mk_mem m in
    let mem_c = mk_mem_c m in
    let inputs = m.mstep.step_inputs in
    let outputs = m.mstep.step_outputs in
    let stateless = fst (get_stateless_status m) in
    let stateless_c = fst (get_stateless_status m_c) in
    let l = List.init (k - 1) (fun n -> n + 1) in
    pp_print_list
      ~pp_open_box:pp_open_vbox0
      ~pp_sep:pp_print_cutcut
      (fun fmt n ->
        let l = List.init (n + 1) (fun n -> n) in
        let pp fmt =
          let pp =
            pp_implies
              (pp_and_l (fun fmt -> function
                 | 0 ->
                   let pp = pp_init pp_print_string in
                   (if stateless_c then fun fmt (x, _) -> pp fmt x
                   else pp_and pp pp)
                     fmt
                     ((name, rename 0 mem), (name_c, rename 0 mem_c))
                 | n' ->
                   let pp_var_c fmt (out, vd) =
                     if out && n' < n then pp_true_c_bool fmt ()
                     else pp_var_decl fmt vd
                   in
                   let c_inputs =
                     List.map
                       (fun v -> false, rename_var_decl n' v)
                       m_c.mstep.step_inputs
                   in
                   let c_outputs =
                     List.map
                       (fun v -> true, rename_var_decl n' v)
                       m_c.mstep.step_outputs
                   in
                   let pp stateless pp_var =
                     pp_transition_aux
                       stateless
                       pp_print_string
                       pp_print_string
                       pp_var
                   in
                   pp_and
                     (pp stateless pp_var_decl)
                     (pp stateless_c pp_var_c)
                     fmt
                     ( ( name,
                         List.map (rename_var_decl n') (inputs @ outputs),
                         rename (n' - 1) mem,
                         rename n' mem ),
                       ( name_c,
                         c_inputs @ c_outputs,
                         rename (n' - 1) mem_c,
                         rename n' mem_c ) )))
              (pp_contract m)
          in
          if stateless_c then pp fmt
          else fun x ->
            pp_forall
              (pp_machine_decl
                 ~ghost:true
                 (pp_comma_list (fun fmt n ->
                      pp_print_string fmt (rename n mem_c))))
              pp
              fmt
              ((name_c, l), x)
        in
        pp_predicate
          (pp_k_induction_base_case
             m
             (pp_machine_decl' ~ghost:true)
             (pp_machine_decl' ~ghost:true)
             (fun fmt xs -> pp_locals m fmt (List.map (rename_var_decl n) xs)))
          (pp_forall
             (pp_locals m)
             (if n > 1 then
              pp_forall
                (fun fmt l ->
                  fprintf
                    fmt
                    "%a@,%a"
                    (pp_machine_decl
                       ~ghost:true
                       (pp_comma_list ~pp_eol:pp_print_comma (fun fmt n ->
                            pp_print_string fmt (rename n mem))))
                    (name, but_last l)
                    (pp_locals m)
                    (List.flatten
                       (List.map
                          (fun n ->
                            List.map (rename_var_decl n) (inputs @ outputs))
                          (List.tl l))))
                pp
             else fun fmt (_, x) -> pp fmt x))
          fmt
          ( (n, (name, rename (n - 1) mem), (name, rename n mem)),
            ( List.map (rename_var_decl n) m_c.mstep.step_outputs,
              (but_last l, (l, rename_contract n c)) ) ))
      fmt
      l

  let pp_inductive_case m fmt (c, m_c, k) =
    let name = m.mname.node_id in
    let mem = mk_mem m in
    let mem_c = mk_mem_c m_c in
    let inputs = m.mstep.step_inputs in
    let outputs = m.mstep.step_outputs in
    let stateless = fst (get_stateless_status m) in
    let stateless_c = fst (get_stateless_status m_c) in
    let l = List.init k (fun n -> n + 1) in
    let l' = 0 :: l in
    let pp fmt =
      let pp =
        pp_implies
          (pp_and_l (fun fmt n ->
               let pp_var_c fmt (out, vd) =
                 if out && n < k then pp_true_c_bool fmt ()
                 else pp_var_decl fmt vd
               in
               let c_inputs =
                 List.map
                   (fun v -> false, rename_var_decl n v)
                   m_c.mstep.step_inputs
               in
               let c_outputs =
                 List.map
                   (fun v -> true, rename_var_decl n v)
                   m_c.mstep.step_outputs
               in
               pp_and
                 (pp_transition_aux
                    stateless
                    pp_print_string
                    pp_print_string
                    pp_var_decl)
                 (pp_transition_aux
                    stateless_c
                    pp_print_string
                    pp_print_string
                    pp_var_c)
                 fmt
                 ( ( name,
                     List.map (rename_var_decl n) (inputs @ outputs),
                     rename (n - 1) mem,
                     rename n mem ),
                   ( m_c.mname.node_id,
                     c_inputs @ c_outputs,
                     rename (n - 1) mem_c,
                     rename n mem_c ) )))
          (pp_contract m)
      in
      if stateless_c then pp fmt
      else fun x ->
        pp_forall
          (pp_machine_decl
             ~ghost:true
             (pp_comma_list (fun fmt n -> pp_print_string fmt (rename n mem_c))))
          pp
          fmt
          ((m_c.mname.node_id, l'), x)
    in
    pp_predicate
      (pp_k_induction_inductive_case
         m
         (pp_machine_decl' ~ghost:true)
         (pp_machine_decl' ~ghost:true)
         (fun fmt xs -> pp_locals m fmt (List.map (rename_var_decl k) xs)))
      (pp_forall
         (pp_locals m)
         (if k > 1 then
          pp_forall
            (fun fmt l ->
              fprintf
                fmt
                "%a@,%a"
                (pp_machine_decl
                   ~ghost:true
                   (pp_comma_list ~pp_eol:pp_print_comma (fun fmt n ->
                        pp_print_string fmt (rename (n - 1) mem))))
                (name, but_last l)
                (pp_locals m)
                (List.flatten
                   (List.map
                      (fun n ->
                        List.map (rename_var_decl (n - 1)) (inputs @ outputs))
                      (List.tl l))))
            pp
         else fun fmt (_, x) -> pp fmt x))
      fmt
      ( (k, (name, rename (k - 1) mem), (name, rename k mem)),
        ( List.map (rename_var_decl k) m_c.mstep.step_outputs,
          (l, (l, rename_contract k c)) ) )

  let pp_k_induction_lemmas m fmt k =
    let name = m.mname.node_id in
    let mem_in = mk_mem_in m in
    let mem_out = mk_mem_out m in
    let inputs = m.mstep.step_inputs in
    let outputs = m.mstep.step_outputs in
    let l = List.init k (fun n -> n + 1) in
    pp_print_list
      ~pp_open_box:pp_open_vbox0
      ~pp_sep:pp_print_cutcut
      (fun fmt n ->
        pp_lemma
          (fun fmt n -> fprintf fmt "%s_k_induction_%d" name n)
          (pp_forall
             (fun fmt () ->
               fprintf
                 fmt
                 "%a,@;%a"
                 (pp_machine_decl ~ghost:true (pp_comma_list pp_print_string))
                 (name, [ mem_in; mem_out ])
                 (pp_locals m)
                 (inputs @ outputs))
             ((if n = k then pp_k_induction_inductive_case
              else pp_k_induction_base_case)
                m
                pp_print_string
                pp_print_string
                (pp_comma_list pp_var_decl)))
          fmt
          (n, ((), (n, mem_in, mem_out))))
      fmt
      l

  let pp_k_induction_axiom m fmt (c, m_c, k) =
    let name = m.mname.node_id in
    let mem_in = mk_mem_in m in
    let mem_out = mk_mem_out m in
    let mem_in_c = mk_mem_in_c m_c in
    let mem_out_c = mk_mem_out_c m_c in
    let inputs = m.mstep.step_inputs in
    let outputs = m.mstep.step_outputs in
    let stateless = fst (get_stateless_status m) in
    let stateless_c = fst (get_stateless_status m_c) in
    let l = List.init k (fun n -> n + 1) in
    let pp =
      pp_implies
        (pp_and_l (fun fmt n ->
             (if n = k then pp_k_induction_inductive_case
             else pp_k_induction_base_case)
               m
               pp_print_string
               pp_print_string
               (pp_comma_list pp_var_decl)
               fmt
               (n, mem_in, mem_out)))
        (pp_forall
           (pp_locals m)
           (pp_implies
              (pp_and
                 (pp_transition_aux
                    stateless
                    pp_print_string
                    pp_print_string
                    pp_var_decl)
                 (pp_transition_aux
                    stateless_c
                    pp_print_string
                    pp_print_string
                    pp_var_decl))
              (pp_contract m)))
    in
    pp_axiomatic
      (fun fmt () -> fprintf fmt "%s_k_Induction" name)
      (pp_axiom
         (fun fmt () -> fprintf fmt "%s_k_induction" name)
         (pp_forall
            (fun fmt () ->
              fprintf
                fmt
                "%a,@;%a"
                (pp_machine_decl ~ghost:true (pp_comma_list pp_print_string))
                (name, [ mem_in; mem_out ])
                (pp_locals m)
                (inputs @ outputs))
            (if stateless_c then pp
            else fun fmt x ->
              pp_forall
                (pp_machine_decl ~ghost:true (pp_comma_list pp_print_string))
                pp
                fmt
                ((m_c.mname.node_id, [ mem_in_c; mem_out_c ]), x))))
      fmt
      ( (),
        ( (),
          ( (),
            ( l,
              ( m_c.mstep.step_outputs,
                ( ( (name, inputs @ outputs, mem_in, mem_out),
                    ( m_c.mname.node_id,
                      m_c.mstep.step_inputs @ m_c.mstep.step_outputs,
                      mem_in_c,
                      mem_out_c ) ),
                  c ) ) ) ) ) )

  let pp_k_induction m fmt ((_, m_c, k) as c_m_k) =
    let stateless_c = fst (get_stateless_status m_c) in
    pp_acsl_cut
      (fun fmt () ->
        fprintf
          fmt
          "%a@,@,%a@,@,%a@,@,%a@,@,%a@,@,%a"
          pp_init_def
          m
          (if stateless_c then pp_print_nothing else pp_init_def)
          m_c
          (pp_base_cases m)
          c_m_k
          (pp_inductive_case m)
          c_m_k
          (pp_k_induction_lemmas m)
          k
          (pp_k_induction_axiom m)
          c_m_k)
      fmt
      ()

  let pp_proof_annotation m m_c fmt c =
    let pp m_c fmt = function
      | Kinduction k ->
        pp_k_induction m fmt (c, m_c, k)
    in
    match m_c with
    | Some m_c ->
      pp_print_option (pp m_c) fmt c.mc_proof
    | None ->
      ()

  let pp_step_spec fmt machines self mem m =
    let name = m.mname.node_id in
    let insts = instances machines m in
    let insts_no_arrow =
      List.(
        filter
          (fun path ->
            let _, (td, _) = hd (rev path) in
            not (Arrow.td_is_arrow td))
          insts)
    in
    let stateful_insts =
      List.(
        filter
          (fun path ->
            let _, (_, mems) = hd (rev path) in
            mems <> [])
          insts)
    in
    let inputs = m.mstep.step_inputs in
    let outputs = m.mstep.step_outputs in
    let stateless = fst (get_stateless_status m) in
    let pp_if_outputs pp = if outputs = [] then pp_print_nothing else pp in
    let c, m_c = contract_of machines m in
    let pp_spec =
      pp_print_option
        (if m.mis_contract then pp_print_nothing
        else fun fmt c ->
          pp_print_option
            (fun fmt m_c ->
              let mem_in = mk_mem_in_c m_c in
              let mem_out = mk_mem_out_c m_c in
              let stateless_c = fst (get_stateless_status m_c) in
              pp_ensures
                (pp_forall
                   (fun fmt vs ->
                      fprintf fmt "%a%a"
                        (if stateless_c then pp_print_nothing
                         else
                           pp_machine_decl
                             ~ghost:true
                             (pp_comma_list ~pp_eol:pp_print_comma pp_print_string))
                        (m_c.mname.node_id, [ mem_in; mem_out ])
                        (pp_locals m) vs)
                  (pp_implies
                     (pp_transition_aux
                        stateless_c
                        pp_print_string
                        pp_print_string
                        (fun fmt v ->
                           (if is_output m v then pp_ptr_decl else pp_var_decl)
                             fmt
                             v))
                     (pp_contract m)))
                  fmt
                (m_c.mstep.step_outputs, ( ( m_c.mname.node_id,
                    m_c.mstep.step_inputs @ m_c.mstep.step_outputs,
                    mem_in,
                    mem_out ),
                  c )))
            fmt
            m_c)
    in
    (* let pp_spec_vars = *)
    (*   match m_c with *)
    (*   | Some m_c -> *)
    (*     let mem_in = mk_mem_in_c m_c in *)
    (*     let mem_out = mk_mem_out_c m_c in *)
    (*     let stateless_c = fst (get_stateless_status m_c) in *)
    (*     pp_acsl_cut *)
    (*       (pp_ghost (fun fmt () -> *)
    (*            fprintf *)
    (*              fmt *)
    (*              "@;<0 2>@[<v>%a%a@]" *)
    (*              (pp_print_list *)
    (*                 ~pp_open_box:pp_open_vbox0 *)
    (*                 ~pp_sep:pp_print_semicolon *)
    (*                 ~pp_eol:pp_print_semicolon *)
    (*                 (pp_c_decl_local_var m)) *)
    (*              m_c.mstep.step_outputs *)
    (*              (if stateless_c then pp_print_nothing *)
    (*              else *)
    (*                pp_machine_decl *)
    (*                  ~ghost:true *)
    (*                  (pp_comma_list ~pp_eol:pp_print_semicolon pp_print_string)) *)
    (*              (m_c.mname.node_id, [ mem_in; mem_out ]))) *)
    (*   | _ -> *)
    (*     pp_print_nothing *)
    (* in *)
    pp_print_option (pp_proof_annotation m m_c) fmt c;
    (* pp_spec_vars fmt (); *)
    pp_acsl_cut
      (fun fmt () ->
        if stateless then
          fprintf
            fmt
            "%a@,%a@,%a@,%a@,%a"
            (pp_if_outputs (pp_requires (pp_valid pp_var_decl)))
            outputs
            (pp_if_outputs (pp_requires pp_separated''))
            outputs
            (pp_assigns pp_ptr_decl)
            outputs
            (pp_ensures (pp_transition_aux' m))
            (name, inputs @ outputs, "", "")
            pp_spec
            c
        else
          fprintf
            fmt
            "%a@,%a@,%a@,%a@,%a@,%a@,%a@,%a@,%a@,%a@,%a@,%a@,%a@,%a@,%a@,%a"
            (pp_if_outputs (pp_requires (pp_valid pp_var_decl)))
            outputs
            (pp_requires pp_mem_valid')
            (name, self)
            (pp_requires (pp_separated' self mem))
            (insts, outputs)
            (pp_requires (pp_memory_pack_aux pp_ptr pp_print_string))
            (name, mem, self)
            (pp_ensures (pp_memory_pack_aux pp_ptr pp_print_string))
            (name, mem, self)
            (pp_ensures
               (pp_transition_aux stateless (pp_old pp_ptr) pp_ptr (fun fmt v ->
                    (if is_output m v then pp_ptr_decl else pp_var_decl) fmt v)))
            (name, inputs @ outputs, mem, mem)
            pp_spec
            c
            (pp_assigns pp_ptr_decl)
            outputs
            (if m.mmemory = [] then pp_print_nothing
            else pp_assigns (pp_reg self))
            [ [] ]
            (pp_assigns pp_reset_flag')
            [ self ]
            (pp_assigns (pp_reg self))
            stateful_insts
            (pp_assigns (pp_reset_flag_chain self))
            insts_no_arrow
            (if m.mmemory = [] then pp_print_nothing
            else pp_assigns (pp_reg mem))
            [ [] ]
            (pp_assigns pp_reset_flag')
            [ mem ]
            (pp_assigns (pp_reg ~indirect:false mem))
            stateful_insts
            (pp_assigns (pp_reset_flag_chain ~indirect:false mem))
            insts_no_arrow)
      fmt
      ()

  let pp_ghost_instr_code m self fmt instr =
    match instr.instr_desc with
    | MStateAssign (x, v) ->
      fprintf
        fmt
        "@,%a"
        (pp_acsl_line (pp_ghost (pp_assign m self (pp_c_var_read m))))
        (x, v)
    | MResetAssign b ->
      fprintf fmt "@,%a" (pp_acsl_line (pp_ghost (pp_reset_assign self))) b
    | MSetReset inst ->
      let td, _ = List.assoc inst m.minstances in
      if Arrow.td_is_arrow td then
        fprintf
          fmt
          "@,%a;"
          (pp_acsl_line (pp_ghost (pp_arrow_reset_ghost self)))
          inst
    | _ ->
      ()

  let pp_step_instr_spec m self mem fmt instr =
    let ghost = m.mis_contract in
    fprintf
      fmt
      "%a%a"
      (pp_ghost_instr_code m mem)
      instr
      (pp_print_list
         ~pp_open_box:pp_open_vbox0
         ~pp_prologue:pp_print_cut
         (pp_acsl_line'
            ~ghost
            (fun fmt (spec, asrt) ->
               let pp = PrintSpec.pp_spec (InstrMode self) m in
               (if asrt then pp_assert pp else pp) fmt spec)))
      instr.instr_spec

  let pp_ghost_parameter mem fmt inst =
    GhostProto.pp_ghost_parameters
      ~cut:false
      fmt
      (match inst with
      | Some inst ->
        [ (inst, fun fmt inst -> pp_ref pp_indirect' fmt (mem, inst)) ]
      | None ->
        [ mem, pp_print_string ])

  let pp_contract fmt machines _self mem m =
    let pp_vars ?pp_eol = pp_comma_list ?pp_eol (pp_c_var_read m) in
    match contract_of machines m with
    | Some c, Some _ ->
      pp_print_option
        (pp_acsl_cut (fun fmt -> function
           | Kinduction k ->
             let l = List.init k (fun n -> n + 1) in
             let pp_mem_in = pp_at_pre pp_ptr in
             let pp_mem_out = pp_ptr in
             pp_assert
               (pp_and_l (fun fmt n ->
                    (if n = k then pp_k_induction_inductive_case
                    else pp_k_induction_base_case)
                      m
                      pp_mem_in
                      pp_mem_out
                      pp_vars
                      fmt
                      (n, mem, mem)))
               fmt
               l))
        fmt
        c.mc_proof
    | _, _ ->
      ()

  let pp_c_decl_local_spec_var m fmt v =
    pp_acsl_line'
      (fun fmt v ->
         fprintf fmt "%a;"
           (pp_ghost (pp_c_decl_local_var m))
           v)
      fmt v

  let get_spec_locals m =
    let rec gather vs instr =
      let vs = List.fold_left (fun vs (spec, _) -> match Spec_common.red spec with
          | Predicate (GhostAssign (v, _)) -> VSet.add v vs
          | _ -> vs) vs instr.instr_spec
      in
      match instr.instr_desc with
      | MBranch (_, hl) ->
        List.fold_left (fun vs (_, il) -> List.fold_left gather vs il) vs hl
      | _ -> vs
    in
    List.fold_left gather VSet.empty m.mstep.step_instrs |> VSet.elements

  let pp_ghost_reset_memory m fmt mem =
    let name = m.mname.node_id in
    let mem_r = mk_mem_reset m in
    pp_acsl_line'
      (pp_ghost
         (fun fmt () ->
            fprintf fmt "%a = %a;"
              (pp_machine_decl' ~ghost:true)
              (name, mem_r)
              pp_ptr mem))
      fmt
      ()

end

module MainMod = struct
  let main_mem_ghost = "main_mem_ghost"

  let pp_declare_ghost_state fmt name =
    pp_acsl_line'_cut
      (pp_ghost (fun fmt () ->
           fprintf
             fmt
             "%a(,%s);"
             (pp_machine_static_alloc_name ~ghost:true)
             name
             main_mem_ghost))
      fmt
      ()

  let pp_ghost_state_parameter fmt () =
    GhostProto.pp_ghost_parameters
      ~cut:false
      fmt
      [ main_mem_ghost, pp_ref pp_print_string ]

  let pp_main_loop_invariants main_mem machines fmt m =
    let name = m.mname.node_id in
    let insts = instances machines m in
    pp_acsl_cut
      (fun fmt () ->
        fprintf
          fmt
          "%a@,%a@,%a@,%a"
          (pp_loop_invariant pp_mem_valid')
          (name, main_mem)
          (pp_loop_invariant
             (pp_memory_pack_aux pp_print_string pp_print_string))
          (name, main_mem_ghost, main_mem)
          (pp_loop_invariant
             (pp_separated
                (pp_paren pp_print_string)
                pp_ref'
                (pp_ref pp_var_decl)))
          (main_mem, main_mem_ghost, insts, m.mstep.step_outputs)
          (pp_loop_invariant
             (pp_or (pp_valid_read pp_stdout) (pp_equal pp_stdout pp_null)))
          ((), ((), ())))
      fmt
      ()

  let pp_main_spec fmt =
    pp_acsl_cut
      (fun fmt () ->
        fprintf
          fmt
          "%a@,%a@,%a@,%a"
          (pp_requires
             (pp_or (pp_valid_read pp_stdout) (pp_equal pp_stdout pp_null)))
          ((), ((), ()))
          (pp_terminates pp_false)
          ()
          (pp_ensures pp_false)
          ()
          (pp_assigns pp_nothing)
          [ () ])
      fmt
      ()
end

(**************************************************************************)
(*                              MAKEFILE                                  *)
(**************************************************************************)

module MakefileMod = struct
  let pp_print_dependencies = C_backend_makefile.fprintf_dependencies "_spec"

  let pp_arrow_o fmt () = pp_print_string fmt "arrow_spec.o"

  let other_targets fmt basename _nodename dependencies =
    fprintf fmt "FRAMACEACSL=`frama-c -print-share-path`/e-acsl@.";
    (* EACSL version of library file . c *)
    fprintf fmt "%s_eacsl.c: %s.c %s.h@." basename basename basename;
    fprintf
      fmt
      "\tframa-c -e-acsl-full-mmodel -machdep x86_64 -e-acsl %s.c -then-on \
       e-acsl -print -ocode %s_eacsl.c@."
      basename
      basename;
    fprintf fmt "@.";
    fprintf fmt "@.";

    (* EACSL version of library file . c + main .c *)
    fprintf
      fmt
      "%s_main_eacsl.c: %s.c %s.h %s_main.c@."
      basename
      basename
      basename
      basename;
    fprintf
      fmt
      "\tframa-c -e-acsl-full-mmodel -machdep x86_64 -e-acsl %s.c %s_main.c \
       -then-on e-acsl -print -ocode %s_main_eacsl.i@."
      basename
      basename
      basename;
    (* Ugly hack to deal with eacsl bugs *)
    fprintf
      fmt
      "\tgrep -v _fc_stdout %s_main_eacsl.i > %s_main_eacsl.c"
      basename
      basename;
    fprintf fmt "@.";
    fprintf fmt "@.";

    (* EACSL version of binary *)
    fprintf fmt "%s_main_eacsl: %s_main_eacsl.c@." basename basename;
    fprintf
      fmt
      "\t${GCC} -Wno-attributes -I${INC} -I. -c %s_main_eacsl.c@."
      basename;
    (* compiling instrumented lib + main *)
    pp_print_dependencies fmt dependencies;
    fprintf
      fmt
      "\t${GCC} -Wno-attributes -o %s_main_eacsl io_frontend.o %a %s \
       %s_main_eacsl.o %a@."
      basename
      (pp_print_list (fun fmt dep -> fprintf fmt "%s.o" dep.name))
      (C_backend_makefile.compiled_dependencies dependencies)
      ("${FRAMACEACSL}/e_acsl.c "
     ^ "${FRAMACEACSL}/memory_model/e_acsl_bittree.c "
     ^ "${FRAMACEACSL}/memory_model/e_acsl_mmodel.c")
      basename
      (pp_print_list (fun fmt lib -> fprintf fmt "-l%s" lib))
      (C_backend_makefile.lib_dependencies dependencies);
    fprintf fmt "@."
end

(* TODO: complete this list *)
let acsl_keywords = ISet.of_list [ "set" ]

let sanitize x = if ISet.mem x acsl_keywords then "__" ^ x else x

let sanitize_var_decl vd = { vd with var_id = sanitize vd.var_id }

let sanitize_var_decls = List.map sanitize_var_decl

let rec sanitize_value v =
  let value_desc =
    match v.value_desc with
    | Machine_code_types.Var vd ->
      Machine_code_types.Var (sanitize_var_decl vd)
    | Fun (f, vs) ->
      Fun (f, sanitize_values vs)
    | Array vs ->
      Array (sanitize_values vs)
    | Access (v1, v2) ->
      Access (sanitize_value v1, sanitize_value v2)
    | Power (v1, v2) ->
      Power (sanitize_value v1, sanitize_value v2)
    | v ->
      v
  in
  { v with value_desc }

and sanitize_values vs = List.map sanitize_value vs

let sanitize_expr = function
  | Val v ->
    Val (sanitize_value v)
  | Var v ->
    Var (sanitize_var_decl v)
  | e ->
    e

let sanitize_predicate = function
  | Transition (st, f, inst, i, vs, r, mf, mfinsts) ->
    Transition (st, f, inst, i, List.map sanitize_expr vs, r, mf, mfinsts)
  | p ->
    p

let rec sanitize_formula = function
  | Equal (e1, e2) ->
    Equal (sanitize_expr e1, sanitize_expr e2)
  | GEqual (e1, e2) ->
    GEqual (sanitize_expr e1, sanitize_expr e2)
  | And fs ->
    And (sanitize_formulae fs)
  | Or fs ->
    Or (sanitize_formulae fs)
  | Imply (f1, f2) ->
    Imply (sanitize_formula f1, sanitize_formula f2)
  | Exists (vs, f) ->
    Exists (sanitize_var_decls vs, sanitize_formula f)
  | Forall (vs, f) ->
    Forall (sanitize_var_decls vs, sanitize_formula f)
  | Ternary (e, t, f) ->
    Ternary (sanitize_expr e, sanitize_formula t, sanitize_formula f)
  | Predicate p ->
    Predicate (sanitize_predicate p)
  | ExistsMem (m, f1, f2) ->
    ExistsMem (m, sanitize_formula f1, sanitize_formula f2)
  | Value v ->
    Value (sanitize_value v)
  | f ->
    f
and sanitize_formulae fs = List.map (fun spec -> sanitize_formula spec) fs

let sanitize_spec fs = List.map (fun (spec, asrt) -> sanitize_formula spec, asrt) fs

let rec sanitize_instr i =
  let sanitize_instr_desc = function
    | MLocalAssign (x, v) ->
      MLocalAssign (sanitize_var_decl x, sanitize_value v)
    | MStateAssign (x, v) ->
      MStateAssign (x, sanitize_value v)
    | MStep (xs, f, vs) ->
      MStep (sanitize_var_decls xs, f, sanitize_values vs)
    | MBranch (v, brs) ->
      MBranch
        ( sanitize_value v,
          List.map (fun (t, instrs) -> t, sanitize_instrs instrs) brs )
    | i ->
      i
  in
  {
    i with
    instr_desc = sanitize_instr_desc i.instr_desc;
    instr_spec = sanitize_spec i.instr_spec;
  }

and sanitize_instrs instrs = List.map sanitize_instr instrs

let sanitize_step s =
  {
    s with
    step_inputs = sanitize_var_decls s.step_inputs;
    step_outputs = sanitize_var_decls s.step_outputs;
    step_locals = sanitize_var_decls s.step_locals;
    step_instrs = sanitize_instrs s.step_instrs;
  }

let sanitize_transition t =
  {
    t with
    tvars = sanitize_var_decls t.tvars;
    tformula = sanitize_formula t.tformula;
  }

let sanitize_transitions = List.map sanitize_transition

let sanitize_memory_pack mp =
  { mp with mpformula = sanitize_formula mp.mpformula }

let sanitize_memory_packs (n, mps) = n, List.map sanitize_memory_pack mps

let sanitize_spec s =
  {
    s with
    mtransitions = sanitize_transitions s.mtransitions;
    mmemory_packs = sanitize_memory_packs s.mmemory_packs;
  }

let sanitize_machine m =
  { m with mstep = sanitize_step m.mstep; mspec = sanitize_spec m.mspec }

let sanitize_machines = List.map sanitize_machine

(* Local Variables: *)
(* compile-command:"make -C ../../.." *)
(* End: *)
