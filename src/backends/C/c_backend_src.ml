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
open Corelang
open Machine_code_common
open C_backend_common
module Mpfr = Lustrec_mpfr

module type MODIFIERS_SRC = sig
  module GhostProto : MODIFIERS_GHOST_PROTO

  val pp_predicates : formatter -> machine_t list -> unit

  val pp_set_reset_spec : formatter -> ident -> ident -> machine_t -> unit

  val pp_clear_reset_spec : formatter -> ident -> ident -> machine_t -> unit

  val pp_step_spec :
    formatter -> machine_t list -> ident -> ident -> machine_t -> unit

  val pp_step_instr_spec :
    machine_t -> ident -> ident -> formatter -> instr_t -> unit

  val pp_ghost_parameter : ident -> formatter -> ident option -> unit
end

module EmptyMod = struct
  module GhostProto = EmptyGhostProto

  let pp_predicates _ _ = ()

  let pp_set_reset_spec _ _ _ _ = ()

  let pp_clear_reset_spec _ _ _ _ = ()

  let pp_step_spec _ _ _ _ _ = ()

  let pp_step_instr_spec _ _ _ _ _ = ()

  let pp_ghost_parameter _ _ _ = ()
end

module Main (Mod : MODIFIERS_SRC) = struct
  module Protos = Protos (Mod.GhostProto)

  (********************************************************************************************)
  (* Instruction Printing functions *)
  (********************************************************************************************)

  (* XXX: UNUSED *)
  (* let rec merge_static_loop_profiles lp1 lp2 =
   *   match lp1, lp2 with
   *   | [], _ ->
   *     lp2
   *   | _, [] ->
   *     lp1
   *   | p1 :: q1, p2 :: q2 ->
   *     (p1 || p2) :: merge_static_loop_profiles q1 q2 *)

  (* XXX: UNUSED *)
  (* Returns a list of bool values, indicating whether the indices must be
     static or not *)
  (* let rec static_loop_profile v =
   *   match v.value_desc with
   *   | Cst cst ->
   *     static_loop_profile_cst cst
   *   | Var _ | ResetFlag ->
   *     []
   *   | Fun (_, vl) ->
   *     List.fold_right
   *       (fun v lp -> merge_static_loop_profiles lp (static_loop_profile v))
   *       vl []
   *   | Array vl ->
   *     true
   *     ::
   *     List.fold_right
   *       (fun v lp -> merge_static_loop_profiles lp (static_loop_profile v))
   *       vl []
   *   | Access (v, _) -> (
   *       match static_loop_profile v with [] -> [] | _ :: q -> q)
   *   | Power (v, _) ->
   *     false :: static_loop_profile v
   *
   * and static_loop_profile_cst cst =
   *   match cst with
   *   | Const_array cl ->
   *     List.fold_right
   *       (fun c lp ->
   *          merge_static_loop_profiles lp (static_loop_profile_cst c))
   *       cl []
   *   | _ ->
   *     [] *)

  (* Subsumes C_backend_common.pp_c_val to cope with aggressive substitution
     which may yield constant arrays in expressions. Type is needed to correctly
     print constant arrays. *)
  let pp_c_val m self pp_var fmt v =
    pp_value_suffix m self v.value_type [] pp_var fmt v

  let pp_machine_ pp_machine_name fn_name m fmt ?inst self mem =
    let name, is_arrow, static =
      match inst with
      | Some inst ->
        let node, static =
          try List.assoc inst m.minstances
          with Not_found ->
            eprintf "internal error: %s %s %s %s:@." fn_name m.mname.node_id
              self inst;
            raise Not_found
        in
        node_name node, Arrow.td_is_arrow node, static
      | None ->
        m.mname.node_id, false, []
    in
    let is_arrow_reset = is_arrow && fn_name = "pp_machine_set_reset" in
    fprintf fmt "%a(%a%s%a)%a;"
      (if is_arrow_reset then fun fmt -> fprintf fmt "%s_reset"
      else pp_machine_name)
      name
      (pp_comma_list ~pp_eol:pp_print_comma Dimension.pp)
      static self
      (pp_print_option (fun fmt -> fprintf fmt "->%s"))
      inst
      (if is_arrow_reset then pp_print_nothing else Mod.pp_ghost_parameter mem)
      inst

  let pp_machine_set_reset m self mem fmt inst =
    pp_machine_ pp_machine_set_reset_name "pp_machine_set_reset" m fmt ~inst
      self mem

  let pp_machine_clear_reset m self mem fmt =
    pp_machine_ pp_machine_clear_reset_name "pp_machine_clear_reset" m fmt self
      mem

  let pp_machine_init m self mem fmt inst =
    pp_machine_ pp_machine_init_name "pp_machine_init" m fmt ~inst self mem

  let pp_machine_clear m self mem fmt inst =
    pp_machine_ pp_machine_clear_name "pp_machine_clear" m fmt ~inst self mem

  let pp_call m self mem pp_read pp_write fmt i inputs outputs =
    try
      (* stateful node instance *)
      let n, _ = List.assoc i m.minstances in
      fprintf fmt "%a(%a%a%s->%s)%a;" pp_machine_step_name (node_name n)
        (pp_comma_list ~pp_eol:pp_print_comma (pp_c_val m self pp_read))
        inputs
        (pp_comma_list ~pp_eol:pp_print_comma pp_write)
        outputs self i
        (Mod.pp_ghost_parameter mem)
        (Some i)
    with Not_found ->
      (* stateless node instance *)
      let n, _ = List.assoc i m.mcalls in
      fprintf fmt "%a(%a%a);" pp_machine_step_name (node_name n)
        (pp_comma_list ~pp_eol:pp_print_comma (pp_c_val m self pp_read))
        inputs (pp_comma_list pp_write) outputs

  let pp_basic_instance_call m self mem =
    pp_call m self mem (pp_c_var_read m) (pp_c_var_write m)

  let pp_arrow_call m self mem fmt i outputs =
    match outputs with
    | [ x ] ->
      fprintf fmt "%a = %a(%s->%s)%a;" (pp_c_var_read m) x pp_machine_step_name
        Arrow.arrow_id self i
        (Mod.pp_ghost_parameter mem)
        (Some i)
    | _ ->
      assert false

  let pp_instance_call m self mem fmt i inputs outputs =
    let pp_offset pp_var indices fmt var =
      fprintf fmt "%a%a" pp_var var
        (pp_print_list ~pp_sep:pp_print_nothing (fun fmt -> fprintf fmt "[%s]"))
        indices
    in
    let rec aux indices fmt typ =
      if Types.is_array_type typ then
        let dim = Types.array_type_dimension typ in
        let idx = mk_loop_var m () in
        fprintf fmt "@[<v 2>{@,int %s;@,for(%s=0;%s<%a;%s++)@,%a @]@,}" idx idx
          idx pp_c_dimension dim idx
          (aux (idx :: indices))
          (Types.array_element_type typ)
      else
        let pp_read = pp_offset (pp_c_var_read m) indices in
        let pp_write = pp_offset (pp_c_var_write m) indices in
        pp_call m self mem pp_read pp_write fmt i inputs outputs
    in
    reset_loop_counter ();
    aux [] fmt (List.hd inputs).Machine_code_types.value_type

  let rec pp_conditional dependencies m self mem fmt c tl el =
    let pp_machine_instrs =
      pp_print_list ~pp_open_box:pp_open_vbox0 ~pp_prologue:pp_print_cut
        (pp_machine_instr dependencies m self mem)
    in
    let pp_cond = pp_c_val m self (pp_c_var_read m) in
    match tl, el with
    | [], _ :: _ ->
      fprintf fmt "@[<v 2>if (!%a) {%a@]@,}" pp_cond c pp_machine_instrs el
    | _, [] ->
      fprintf fmt "@[<v 2>if (%a) {%a@]@,}" pp_cond c pp_machine_instrs tl
    | _, _ ->
      fprintf fmt "@[<v 2>if (%a) {%a@]@,@[<v 2>} else {%a@]@,}" pp_cond c
        pp_machine_instrs tl pp_machine_instrs el

  and pp_machine_instr dependencies m self mem fmt instr =
    let pp_instr fmt instr =
      match get_instr_desc instr with
      | MNoReset _ ->
        ()
      | MSetReset inst ->
        pp_machine_set_reset m self mem fmt inst
      | MClearReset ->
        if not (fst (get_stateless_status m)) then
          fprintf fmt "%t@,%a"
            (pp_machine_clear_reset m self mem)
            pp_label reset_label
      | MResetAssign b ->
        pp_reset_assign self fmt b
      | MLocalAssign (i, v) ->
        pp_assign m self (pp_c_var_read m) fmt (i, v)
      | MStateAssign (i, v) ->
        pp_assign m self (pp_c_var_read m) fmt (i, v)
      | MStep ([ i0 ], i, vl)
        when Basic_library.is_value_internal_fun
               (mk_val (Fun (i, vl)) i0.var_type) ->
        pp_machine_instr dependencies m self mem fmt
          (update_instr_desc instr
             (MLocalAssign (i0, mk_val (Fun (i, vl)) i0.var_type)))
      | MStep (il, i, vl) when !Options.mpfr && Mpfr.is_homomorphic_fun i ->
        pp_instance_call m self mem fmt i vl il
      | MStep ([ i0 ], i, vl) when has_c_prototype i dependencies ->
        fprintf fmt "%a = %s%a;"
          (pp_c_val m self (pp_c_var_read m))
          (mk_val (Var i0) i0.var_type)
          i
          (pp_print_parenthesized (pp_c_val m self (pp_c_var_read m)))
          vl
      | MStep (il, i, vl) ->
        let td, _ = List.assoc i m.minstances in
        if Arrow.td_is_arrow td then pp_arrow_call m self mem fmt i il
        else pp_basic_instance_call m self mem fmt i vl il
      | MBranch (_, []) ->
        eprintf "internal error: C_backend_src.pp_machine_instr %a@."
          (pp_instr m) instr;
        assert false
      | MBranch (g, hl) ->
        if
          let t = fst (List.hd hl) in
          t = tag_true || t = tag_false
        then
          (* boolean case, needs special treatment in C because truth value is
             not unique *)
          (* may disappear if we optimize code by replacing last branch test
             with default *)
          let tl = try List.assoc tag_true hl with Not_found -> [] in
          let el = try List.assoc tag_false hl with Not_found -> [] in
          let no_noreset =
            List.filter (fun i ->
                match i.instr_desc with MNoReset _ -> false | _ -> true)
          in
          pp_conditional dependencies m self mem fmt g (no_noreset tl)
            (no_noreset el)
        else
          (* enum type case *)
          (*let g_typ = Typing.type_const Location.dummy_loc (Const_tag (fst
            (List.hd hl))) in*)
          fprintf fmt "@[<v 2>switch(%a) {@,%a@,}@]"
            (pp_c_val m self (pp_c_var_read m))
            g
            (pp_print_list ~pp_open_box:pp_open_vbox0
               (pp_machine_branch dependencies m self mem))
            hl
      | MSpec s ->
        fprintf fmt "@[/*@@ %s */@]@ " s
      | MComment s ->
        fprintf fmt "/*%s*/@ " s
    in
    fprintf fmt "%a%a" pp_instr instr (Mod.pp_step_instr_spec m self mem) instr

  and pp_machine_branch dependencies m self mem fmt (t, h) =
    fprintf fmt "@[<v 2>case %a:@,%a@,break;@]" pp_c_tag t
      (pp_print_list ~pp_open_box:pp_open_vbox0
         (pp_machine_instr dependencies m self mem))
      h

  (* let pp_machine_nospec_instr dependencies m self fmt instr =
   *   pp_machine_instr dependencies m self fmt instr
   *
   * let pp_machine_step_instr dependencies m self mem fmt instr =
   *   fprintf fmt "%a%a"
   *     (pp_machine_instr dependencies m self) instr
   *     (Mod.pp_step_instr_spec m self mem) instr *)

  (********************************************************************************************)
  (* C file Printing functions *)
  (********************************************************************************************)

  let print_const_def fmt tdecl =
    let cdecl = const_of_top tdecl in
    if !Options.mpfr && Types.(is_real_type (array_base_type cdecl.const_type))
    then
      fprintf fmt "%a;" (pp_c_type cdecl.const_id)
        (Types.dynamic_type cdecl.const_type)
    else
      fprintf fmt "%a = %a;" (pp_c_type cdecl.const_id) cdecl.const_type
        pp_c_const cdecl.const_value

  let print_alloc_instance fmt (i, (m, static)) =
    fprintf fmt "_alloc->%s = %a %a;" i pp_machine_alloc_name (node_name m)
      (pp_print_parenthesized Dimension.pp)
      static

  let print_dealloc_instance fmt (i, (m, _)) =
    fprintf fmt "%a (_alloc->%s);" pp_machine_dealloc_name (node_name m) i

  let const_locals m =
    List.filter (fun vdecl -> vdecl.var_dec_const) m.mstep.step_locals

  let pp_c_decl_array_mem self fmt id =
    fprintf fmt "%a = (%a) (%s->_reg.%s)"
      (pp_c_type (sprintf "(*%s)" id.var_id))
      id.var_type (pp_c_type "(*)") id.var_type self id.var_id

  let print_alloc_const fmt m =
    pp_print_list ~pp_sep:(pp_print_endcut ";") ~pp_eol:(pp_print_endcut ";")
      (pp_c_decl_local_var m) fmt (const_locals m)

  let print_alloc_array fmt vdecl =
    let base_type = Types.array_base_type vdecl.var_type in
    let size_types = Types.array_type_multi_dimension vdecl.var_type in
    let size_type = Dimension.multi_product vdecl.var_loc size_types in
    fprintf fmt
      "_alloc->_reg.%s = (%a*) malloc((%a)*sizeof(%a));@,assert(_alloc->%s);"
      vdecl.var_id (pp_c_type "") base_type Dimension.pp size_type
      (pp_c_type "") base_type vdecl.var_id

  let print_dealloc_array fmt vdecl =
    fprintf fmt "free (_alloc->_reg.%s);" vdecl.var_id

  let array_mems m =
    List.filter (fun v -> Types.is_array_type v.var_type) m.mmemory

  let print_alloc_code fmt m =
    fprintf fmt
      "%a *_alloc;@,\
       _alloc = (%a *) malloc(sizeof(%a));@,\
       assert(_alloc);@,\
       %a%areturn _alloc;"
      (pp_machine_memtype_name ~ghost:false)
      m.mname.node_id
      (pp_machine_memtype_name ~ghost:false)
      m.mname.node_id
      (pp_machine_memtype_name ~ghost:false)
      m.mname.node_id
      (pp_print_list ~pp_sep:pp_print_nothing print_alloc_array)
      (array_mems m)
      (pp_print_list ~pp_sep:pp_print_nothing print_alloc_instance)
      m.minstances

  let print_dealloc_code fmt m =
    fprintf fmt "%a%afree (_alloc);@,return;"
      (pp_print_list ~pp_sep:pp_print_nothing print_dealloc_array)
      (array_mems m)
      (pp_print_list ~pp_sep:pp_print_nothing print_dealloc_instance)
      m.minstances

  (* let print_stateless_init_code fmt m self =
   *   let minit = List.map (fun i -> match get_instr_desc i with MReset i -> i | _ -> assert false) m.minit in
   *   let array_mems = List.filter (fun v -> Types.is_array_type v.var_type) m.mmemory in
   *   fprintf fmt "@[<v 2>%a {@,%a%t%a%t%a%treturn;@]@,}@.@."
   *     (print_init_prototype self) (m.mname.node_id, m.mstatic)
   *     (\* array mems *\)
   *     (Utils.fprintf_list ~sep:";@," (pp_c_decl_array_mem self)) array_mems
   *     (Utils.pp_final_char_if_non_empty ";@," array_mems)
   *     (\* memory initialization *\)
   *     (Utils.fprintf_list ~sep:"@," (pp_initialize m self (pp_c_var_read m))) m.mmemory
   *     (Utils.pp_newline_if_non_empty m.mmemory)
   *     (\* sub-machines initialization *\)
   *     (Utils.fprintf_list ~sep:"@," (pp_machine_init m self)) minit
   *     (Utils.pp_newline_if_non_empty m.minit)
   *
   * let print_stateless_clear_code fmt m self =
   *   let minit = List.map (fun i -> match get_instr_desc i with MReset i -> i | _ -> assert false) m.minit in
   *   let array_mems = List.filter (fun v -> Types.is_array_type v.var_type) m.mmemory in
   *   fprintf fmt "@[<v 2>%a {@,%a%t%a%t%a%treturn;@]@,}@.@."
   *     (print_clear_prototype self) (m.mname.node_id, m.mstatic)
   *     (\* array mems *\)
   *     (Utils.fprintf_list ~sep:";@," (pp_c_decl_array_mem self)) array_mems
   *     (Utils.pp_final_char_if_non_empty ";@," array_mems)
   *     (\* memory clear *\)
   *     (Utils.fprintf_list ~sep:"@," (pp_clear m self (pp_c_var_read m))) m.mmemory
   *     (Utils.pp_newline_if_non_empty m.mmemory)
   *     (\* sub-machines clear*\)
   *     (Utils.fprintf_list ~sep:"@," (pp_machine_clear m self)) minit
   *     (Utils.pp_newline_if_non_empty m.minit) *)

  let pp_c_check m self fmt (loc, check) =
    fprintf fmt "@[<v>%a@,assert (%a);@]" Location.pp_c loc
      (pp_c_val m self (pp_c_var_read m))
      check

  let pp_print_function ~pp_prototype ~prototype ?(pp_spec = pp_print_nothing)
      ?(pp_local = pp_print_nothing) ?(base_locals = [])
      ?(pp_array_mem = pp_print_nothing) ?(array_mems = [])
      ?(pp_init_mpfr_local = pp_print_nothing)
      ?(pp_clear_mpfr_local = pp_print_nothing) ?(mpfr_locals = [])
      ?(pp_check = pp_print_nothing) ?(checks = [])
      ?(pp_extra = pp_print_nothing)
      ?(pp_instr = fun fmt _ -> pp_print_nothing fmt ()) ?(instrs = []) fmt =
    fprintf fmt "%a@[<v 2>%a {@,%a%a%a%a%a%a%areturn;@]@,}" pp_spec ()
      pp_prototype prototype
      (* locals *)
      (pp_print_list ~pp_open_box:pp_open_vbox0 ~pp_sep:pp_print_semicolon
         ~pp_eol:pp_print_semicolon pp_local)
      base_locals
      (* array mems *)
      (pp_print_list ~pp_open_box:pp_open_vbox0 ~pp_sep:pp_print_semicolon
         ~pp_eol:pp_print_semicolon pp_array_mem)
      array_mems
      (* locals initialization *)
      (pp_print_list ~pp_epilogue:pp_print_cut pp_init_mpfr_local)
      (mpfr_vars mpfr_locals)
      (* check assertions *)
      (pp_print_list pp_check)
      checks
      (* instrs *)
      (pp_print_list ~pp_open_box:pp_open_vbox0 ~pp_epilogue:pp_print_cut
         pp_instr)
      instrs
      (* locals clear *)
      (pp_print_list ~pp_epilogue:pp_print_cut pp_clear_mpfr_local)
      (mpfr_vars mpfr_locals) (* extra *)
      pp_extra ()

  let node_of_machine m =
    {
      top_decl_desc = Node m.mname;
      top_decl_loc = Location.dummy;
      top_decl_owner = "";
      top_decl_itf = false;
    }

  let print_stateless_code machines dependencies fmt m =
    let self = "__ERROR__" in
    if not (!Options.ansi && is_generic_node (node_of_machine m)) then
      (* C99 code *)
      pp_print_function
        ~pp_spec:(fun fmt () -> Mod.pp_step_spec fmt machines self self m)
        ~pp_prototype:Protos.print_stateless_prototype
        ~prototype:(m.mname.node_id, m.mstep.step_inputs, m.mstep.step_outputs)
        ~pp_local:(pp_c_decl_local_var m) ~base_locals:m.mstep.step_locals
        ~pp_init_mpfr_local:(pp_initialize m self (pp_c_var_read m))
        ~pp_clear_mpfr_local:(pp_clear m self (pp_c_var_read m))
        ~mpfr_locals:m.mstep.step_locals ~pp_check:(pp_c_check m self)
        ~checks:m.mstep.step_checks
        ~pp_instr:(pp_machine_instr dependencies m self self)
        ~instrs:m.mstep.step_instrs fmt
    else
      (* C90 code *)
      let gen_locals, base_locals =
        List.partition
          (fun v -> Types.is_generic_type v.var_type)
          m.mstep.step_locals
      in
      let gen_calls =
        List.map
          (fun e ->
            let id, _, _ = call_of_expr e in
            mk_call_var_decl e.expr_loc id)
          m.mname.node_gencalls
      in
      pp_print_function ~pp_prototype:Protos.print_stateless_prototype
        ~prototype:
          ( m.mname.node_id,
            m.mstep.step_inputs @ gen_locals @ gen_calls,
            m.mstep.step_outputs )
        ~pp_local:(pp_c_decl_local_var m) ~base_locals
        ~pp_init_mpfr_local:(pp_initialize m self (pp_c_var_read m))
        ~pp_clear_mpfr_local:(pp_clear m self (pp_c_var_read m))
        ~mpfr_locals:m.mstep.step_locals ~pp_check:(pp_c_check m self)
        ~checks:m.mstep.step_checks
        ~pp_instr:(pp_machine_instr dependencies m self self)
        ~instrs:m.mstep.step_instrs fmt

  let print_clear_reset_code dependencies self mem fmt m =
    pp_print_function
      ~pp_spec:(fun fmt () -> Mod.pp_clear_reset_spec fmt self mem m)
      ~pp_prototype:(Protos.print_clear_reset_prototype self mem)
      ~prototype:(m.mname.node_id, m.mstatic)
      ~pp_local:(pp_c_decl_local_var m) ~base_locals:(const_locals m)
      ~pp_instr:(pp_machine_instr dependencies m self mem)
      ~instrs:
        [
          mk_branch
            (mk_val ResetFlag Type_predef.type_bool)
            [ "true", mkinstr (MResetAssign false) :: m.minit ];
        ]
      fmt

  let print_set_reset_code dependencies self mem fmt m =
    pp_print_function
      ~pp_spec:(fun fmt () -> Mod.pp_set_reset_spec fmt self mem m)
      ~pp_prototype:(Protos.print_set_reset_prototype self mem)
      ~prototype:(m.mname.node_id, m.mstatic)
      ~pp_instr:(pp_machine_instr dependencies m self mem)
      ~instrs:[ mkinstr (MResetAssign true) ]
      fmt

  let print_init_code self fmt m =
    let minit =
      List.map
        (fun i ->
          match get_instr_desc i with MSetReset i -> i | _ -> assert false)
        m.minit
    in
    pp_print_function
      ~pp_prototype:(Protos.print_init_prototype self)
      ~prototype:(m.mname.node_id, m.mstatic)
      ~pp_array_mem:(pp_c_decl_array_mem self) ~array_mems:(array_mems m)
      ~pp_init_mpfr_local:(pp_initialize m self (pp_c_var_read m))
      ~mpfr_locals:m.mmemory
      ~pp_extra:(fun fmt () ->
        pp_print_list ~pp_open_box:pp_open_vbox0 ~pp_epilogue:pp_print_cut
          (pp_machine_init m self self)
          fmt minit)
      fmt

  let print_clear_code self fmt m =
    let minit =
      List.map
        (fun i ->
          match get_instr_desc i with MSetReset i -> i | _ -> assert false)
        m.minit
    in
    pp_print_function
      ~pp_prototype:(Protos.print_clear_prototype self)
      ~prototype:(m.mname.node_id, m.mstatic)
      ~pp_array_mem:(pp_c_decl_array_mem self) ~array_mems:(array_mems m)
      ~pp_clear_mpfr_local:(pp_clear m self (pp_c_var_read m))
      ~mpfr_locals:m.mmemory
      ~pp_extra:(fun fmt () ->
        pp_print_list ~pp_open_box:pp_open_vbox0 ~pp_epilogue:pp_print_cut
          (pp_machine_clear m self self)
          fmt minit)
      fmt

  let print_step_code machines dependencies self mem fmt m =
    if not (!Options.ansi && is_generic_node (node_of_machine m)) then
      (* C99 code *)
      pp_print_function
        ~pp_spec:(fun fmt () -> Mod.pp_step_spec fmt machines self mem m)
        ~pp_prototype:(Protos.print_step_prototype self mem)
        ~prototype:(m.mname.node_id, m.mstep.step_inputs, m.mstep.step_outputs)
        ~pp_local:(pp_c_decl_local_var m) ~base_locals:m.mstep.step_locals
        ~pp_array_mem:(pp_c_decl_array_mem self) ~array_mems:(array_mems m)
        ~pp_init_mpfr_local:(pp_initialize m self (pp_c_var_read m))
        ~pp_clear_mpfr_local:(pp_clear m self (pp_c_var_read m))
        ~mpfr_locals:m.mstep.step_locals ~pp_check:(pp_c_check m self)
        ~checks:m.mstep.step_checks
        ~pp_instr:(pp_machine_instr dependencies m self mem)
        ~instrs:m.mstep.step_instrs fmt
    else
      (* C90 code *)
      let gen_locals, base_locals =
        List.partition
          (fun v -> Types.is_generic_type v.var_type)
          m.mstep.step_locals
      in
      let gen_calls =
        List.map
          (fun e ->
            let id, _, _ = call_of_expr e in
            mk_call_var_decl e.expr_loc id)
          m.mname.node_gencalls
      in
      pp_print_function
        ~pp_spec:(fun fmt () -> Mod.pp_step_spec fmt machines self mem m)
        ~pp_prototype:(Protos.print_step_prototype self mem)
        ~prototype:
          ( m.mname.node_id,
            m.mstep.step_inputs @ gen_locals @ gen_calls,
            m.mstep.step_outputs )
        ~pp_local:(pp_c_decl_local_var m) ~base_locals
        ~pp_init_mpfr_local:(pp_initialize m self (pp_c_var_read m))
        ~pp_clear_mpfr_local:(pp_clear m self (pp_c_var_read m))
        ~mpfr_locals:m.mstep.step_locals ~pp_check:(pp_c_check m self)
        ~checks:m.mstep.step_checks
        ~pp_instr:(pp_machine_instr dependencies m self mem)
        ~instrs:m.mstep.step_instrs fmt

  (********************************************************************************************)
  (* MAIN C file Printing functions *)
  (********************************************************************************************)

  let pp_const_initialize m pp_var fmt const =
    let var =
      Machine_code_common.mk_val
        (Var (Corelang.var_decl_of_const const))
        const.const_type
    in
    let rec aux indices value fmt typ =
      if Types.is_array_type typ then
        let dim = Types.array_type_dimension typ in
        let szl = Utils.enumerate (Dimension.size_const dim) in
        let typ' = Types.array_element_type typ in
        let value =
          match value with Const_array ca -> List.nth ca | _ -> assert false
        in
        pp_print_list
          (fun fmt i -> aux (string_of_int i :: indices) (value i) fmt typ')
          fmt szl
      else
        let indices = List.rev indices in
        let pp_var_suffix fmt var =
          fprintf fmt "%a%a" (pp_c_val m "" pp_var) var pp_array_suffix indices
        in
        fprintf fmt "%a@,%a"
          (Mpfr.pp_inject_init pp_var_suffix)
          var
          (Mpfr.pp_inject_real pp_var_suffix pp_c_const)
          (var, value)
    in
    reset_loop_counter ();
    aux [] const.const_value fmt const.const_type

  let pp_const_clear pp_var fmt const =
    let m = Machine_code_common.empty_machine in
    let var = Corelang.var_decl_of_const const in
    let rec aux indices fmt typ =
      if Types.is_array_type typ then
        let dim = Types.array_type_dimension typ in
        let idx = mk_loop_var m () in
        fprintf fmt "@[<v 2>{@,int %s;@,for(%s=0;%s<%a;%s++)@,%a @]@,}" idx idx
          idx pp_c_dimension dim idx
          (aux (idx :: indices))
          (Types.array_element_type typ)
      else
        let indices = List.rev indices in
        let pp_var_suffix fmt var =
          fprintf fmt "%a%a" (pp_c_var m "" pp_var) var pp_array_suffix indices
        in
        Mpfr.pp_inject_clear pp_var_suffix fmt var
    in
    reset_loop_counter ();
    aux [] fmt var.var_type

  let print_import_init fmt dep =
    let baseNAME = file_to_module_name dep.name in
    fprintf fmt "%a();" pp_global_init_name baseNAME

  let print_import_clear fmt dep =
    let baseNAME = file_to_module_name dep.name in
    fprintf fmt "%a();" pp_global_clear_name baseNAME

  let print_global_init_code fmt (basename, prog, dependencies) =
    let baseNAME = file_to_module_name basename in
    let constants = List.map const_of_top (get_consts prog) in
    fprintf fmt
      "@[<v 2>%a {@,\
       static %s init = 0;@,\
       @[<v 2>if (!init) { @,\
       init = 1;%a%a@]@,\
       }@,\
       return;@]@,\
       }"
      pp_global_init_prototype baseNAME
      (pp_c_basic_type_desc Type_predef.type_bool)
      (* constants *)
      (pp_print_list ~pp_prologue:pp_print_cut
         (pp_const_initialize empty_machine (pp_c_var_read empty_machine)))
      (mpfr_consts constants)
      (* dependencies initialization *)
      (pp_print_list ~pp_prologue:pp_print_cut print_import_init)
      (List.filter (fun dep -> dep.local) dependencies)

  let print_global_clear_code fmt (basename, prog, dependencies) =
    let baseNAME = file_to_module_name basename in
    let constants = List.map const_of_top (get_consts prog) in
    fprintf fmt
      "@[<v 2>%a {@,\
       static %s clear = 0;@,\
       @[<v 2>if (!clear) { @,\
       clear = 1;%a%a@]@,\
       }@,\
       return;@]@,\
       }"
      pp_global_clear_prototype baseNAME
      (pp_c_basic_type_desc Type_predef.type_bool)
      (* constants *)
      (pp_print_list ~pp_prologue:pp_print_cut
         (pp_const_clear (pp_c_var_read empty_machine)))
      (mpfr_consts constants)
      (* dependencies initialization *)
      (pp_print_list ~pp_prologue:pp_print_cut print_import_clear)
      (List.filter (fun dep -> dep.local) dependencies)

  let print_alloc_function fmt m =
    if not !Options.static_mem then
      (* Alloc functions, only if non static mode *)
      fprintf fmt "@[<v 2>%a {@,%a%a@]@,}@,@[<v 2>%a {@,%a%a@]@,@,"
        pp_alloc_prototype
        (m.mname.node_id, m.mstatic)
        print_alloc_const m print_alloc_code m pp_dealloc_prototype
        m.mname.node_id print_alloc_const m print_dealloc_code m

  let print_mpfr_code self fmt m =
    if !Options.mpfr then
      fprintf fmt "@,@[<v>%a@,%a@]"
        (* Init function *)
        (print_init_code self)
        m
        (* Clear function *)
        (print_clear_code self)
        m

  (* TODO: ACSL - a contract machine shall not be directly printed in the C
     source - but a regular machine associated to a contract machine shall
     integrate the associated statements, updating its memories, at the end of
     the function body. - last one may print intermediate comment/acsl if/when
     they are present in the sequence of instruction *)
  let print_machine machines dependencies fmt m =
    if fst (get_stateless_status m) then
      (* Step function *)
      print_stateless_code machines dependencies fmt m
    else
      let self = mk_self m in
      let mem = mk_mem m in
      fprintf fmt "@[<v>%a%a@,@,%a@,@,%a%a@]" print_alloc_function m
        (* Reset functions *)
        (print_clear_reset_code dependencies self mem)
        m
        (print_set_reset_code dependencies self mem)
        m
        (* Step function *)
        (print_step_code machines dependencies self mem)
        m (print_mpfr_code self) m

  let print_import_standard source_fmt () =
    fprintf source_fmt "@[<v>#include <assert.h>@,%a%a%a@]"
      (if Machine_types.has_machine_type () then
       pp_print_endcut "#include <stdint.h>"
      else pp_print_nothing)
      ()
      (if not !Options.static_mem then pp_print_endcut "#include <stdlib.h>"
      else pp_print_nothing)
      ()
      (if !Options.mpfr then pp_print_endcut "#include <mpfr.h>"
      else pp_print_nothing)
      ()

  let print_extern_alloc_prototype fmt ind =
    let static = List.filter (fun v -> v.var_dec_const) ind.nodei_inputs in
    fprintf fmt "extern %a;@,extern %a;" pp_alloc_prototype
      (ind.nodei_id, static) pp_dealloc_prototype ind.nodei_id

  let print_lib_c source_fmt basename prog machines dependencies =
    fprintf source_fmt "@[<v>%a%a@,@,%a@,%a%a%a%a%a%a%a@]@."
      print_import_standard () pp_import_prototype
      {
        local = true;
        name = basename;
        content = [];
        is_stateful = true (* assuming it is stateful *);
      }
      (* Print the svn version number and the supported C standard (C90 or C99) *)
      pp_print_version ()
      (* Print dependencies *)
      (pp_print_list ~pp_open_box:pp_open_vbox0
         ~pp_prologue:(pp_print_endcut "/* Import dependencies */")
         pp_import_prototype ~pp_epilogue:pp_print_cutcut)
      dependencies
      (* Print consts *)
      (pp_print_list ~pp_open_box:pp_open_vbox0
         ~pp_prologue:(pp_print_endcut "/* Global constants (definitions) */")
         print_const_def ~pp_epilogue:pp_print_cutcut)
      (get_consts prog)
      (* MPFR *)
      (if !Options.mpfr then fun fmt () ->
       fprintf fmt
         "@[<v>/* Global constants initialization */@,\
          %a@,\
          @,\
          /* Global constants clearing */@,\
          %a@]@,\
          @,"
         print_global_init_code
         (basename, prog, dependencies)
         print_global_clear_code
         (basename, prog, dependencies)
      else pp_print_nothing)
      ()
      (if not !Options.static_mem then fun fmt () ->
       fprintf fmt "@[<v>%a%a@]@,@,"
         (pp_print_list ~pp_open_box:pp_open_vbox0 ~pp_epilogue:pp_print_cut
            ~pp_prologue:
              (pp_print_endcut "/* External allocation function prototypes */")
            (fun fmt dep ->
              pp_print_list ~pp_open_box:pp_open_vbox0 ~pp_epilogue:pp_print_cut
                print_extern_alloc_prototype fmt
                (List.filter_map
                   (fun decl ->
                     match decl.top_decl_desc with
                     | ImportedNode ind when not ind.nodei_stateless ->
                       Some ind
                     | _ ->
                       None)
                   dep.content)))
         dependencies
         (pp_print_list ~pp_open_box:pp_open_vbox0
            ~pp_prologue:
              (pp_print_endcut "/* Node allocation function prototypes */")
            ~pp_sep:pp_print_cutcut (fun fmt m ->
              fprintf fmt "%a;@,%a;" pp_alloc_prototype
                (m.mname.node_id, m.mstatic)
                pp_dealloc_prototype m.mname.node_id))
         machines
      else pp_print_nothing)
      ()
      (* Print the struct definitions of all machines. *)
      (pp_print_list ~pp_open_box:pp_open_vbox0
         ~pp_prologue:(pp_print_endcut "/* Struct definitions */")
         ~pp_sep:pp_print_cutcut pp_machine_struct ~pp_epilogue:pp_print_cutcut)
      machines (* Print the spec predicates *) Mod.pp_predicates machines
      (* Print nodes one by one (in the previous order) *)
      (pp_print_list ~pp_open_box:pp_open_vbox0 ~pp_sep:pp_print_cutcut
         (print_machine machines dependencies))
      machines
end

(* Local Variables: *)
(* compile-command:"make -C ../../.." *)
(* End: *)
