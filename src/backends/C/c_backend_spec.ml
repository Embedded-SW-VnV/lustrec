
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

open Utils.Format
open Lustre_types
open Machine_code_types
open C_backend_common
open Corelang
open Spec_types
open Spec_common
open Machine_code_common

(**************************************************************************)
(*     Printing spec for c *)

(**************************************************************************)

(* TODO ACSL
   Return updates machines (eg with local annotations) and acsl preamble *)
let preprocess_acsl machines = machines, []
                          
let pp_acsl_basic_type_desc t_desc =
  if Types.is_bool_type t_desc then
    (* if !Options.cpp then "bool" else "_Bool" *)
    "_Bool"
  else if Types.is_int_type t_desc then
    (* !Options.int_type *)
    "integer"
  else if Types.is_real_type t_desc then
    if !Options.mpfr then Mpfr.mpfr_t else !Options.real_type
  else
    assert false (* Not a basic C type. Do not handle arrays or pointers *)

let pp_acsl pp fmt =
  fprintf fmt "@[<v>/*%@ @[<v>%a@]@,*/@]" pp

let pp_acsl_cut pp fmt =
  fprintf fmt "%a@," (pp_acsl pp)

let pp_acsl_line pp fmt =
  fprintf fmt "//%@ @[<h>%a@]" pp

let pp_requires pp_req fmt =
  fprintf fmt "requires %a;" pp_req

let pp_ensures pp_ens fmt =
  fprintf fmt "ensures %a;" pp_ens

let pp_assumes pp_asm fmt =
  fprintf fmt "assumes %a;" pp_asm

let pp_assigns pp =
  pp_comma_list
    ~pp_prologue:(fun fmt () -> pp_print_string fmt "assigns ")
    ~pp_epilogue:pp_print_semicolon'
    pp

let pp_ghost pp_gho fmt =
  fprintf fmt "ghost %a" pp_gho

let pp_assert pp_ast fmt =
  fprintf fmt "assert %a;" pp_ast

let pp_mem_valid pp_var fmt (name, var) =
  fprintf fmt "%s_valid(%a)" name pp_var var

let pp_mem_valid' = pp_mem_valid pp_print_string

let pp_indirect pp_ptr pp_field fmt (ptr, field) =
  fprintf fmt "%a->%a" pp_ptr ptr pp_field field

let pp_indirect' = pp_indirect pp_print_string pp_print_string

let pp_access pp_stru pp_field fmt (stru, field) =
  fprintf fmt "%a.%a" pp_stru stru pp_field field

let pp_access' = pp_access pp_print_string pp_print_string

let pp_inst self fmt (name, _) =
  pp_indirect' fmt (self, name)

let pp_var_decl fmt v =
  pp_print_string fmt v.var_id

let pp_reg self fmt field =
  pp_access pp_indirect' pp_var_decl fmt ((self, "_reg"), field)

let pp_true fmt () =
  pp_print_string fmt "\\true"

let pp_false fmt () =
  pp_print_string fmt "\\false"

let pp_at pp_v fmt (v, l) =
  fprintf fmt "\\at(%a, %s)" pp_v v l

let instances machines m =
  let open List in
  let grow paths i td mems =
    match paths with
    | [] -> [[i, (td, mems)]]
    | _ -> map (cons (i, (td, mems))) paths
  in
  let rec aux paths m =
    map (fun (i, (td, _)) ->
        try
          let m = find (fun m -> m.mname.node_id = node_name td) machines in
          aux (grow paths i td m.mmemory) m
        with Not_found -> grow paths i td [])
      m.minstances |> flatten
  in
  aux [] m |> map rev

let memories insts =
  List.(map (fun path ->
      let _, (_, mems) = hd (rev path) in
      map (fun mem -> path, mem) mems) insts |> flatten)

let pp_instance ?(indirect=true) ptr =
  pp_print_list
    ~pp_prologue:(fun fmt () -> fprintf fmt "%s->" ptr)
    ~pp_sep:(fun fmt () -> pp_print_string fmt (if indirect then "->" else "."))
    (fun fmt (i, _) -> pp_print_string fmt i)

let pp_memory ?(indirect=true) ptr fmt (path, mem) =
  pp_access
    ((if indirect then pp_indirect else pp_access)
       (pp_instance ~indirect ptr) pp_print_string)
    pp_var_decl
    fmt ((path, "_reg"), mem)

let prefixes l =
  let rec pref acc = function
    | x :: l -> pref ([x] :: List.map (List.cons x) acc) l
    | [] -> acc
  in
  pref [] (List.rev l)

let powerset_instances paths =
  List.map prefixes paths |> List.flatten

let pp_separated self mem fmt (paths, ptrs) =
  fprintf fmt "\\separated(@[<v>%s, %s@;%a@;%a@])"
    self
    mem
    (pp_comma_list
       ~pp_prologue:pp_print_comma'
       (pp_instance self))
    paths
    (pp_comma_list
       ~pp_prologue:pp_print_comma'
       pp_var_decl)
    ptrs

let pp_separated' =
  pp_comma_list
    ~pp_prologue:(fun fmt () -> pp_print_string fmt "\\separated(")
    ~pp_epilogue:pp_print_cpar
    pp_var_decl

let pp_par pp fmt =
  fprintf fmt "(%a)" pp

let pp_forall pp_l pp_r fmt (l, r) =
  fprintf fmt "@[<v 2>\\forall %a;@,%a@]"
    pp_l l
    pp_r r

let pp_exists pp_l pp_r fmt (l, r) =
  fprintf fmt "@[<v 2>\\exists %a;@,%a@]"
    pp_l l
    pp_r r

let pp_equal pp_l pp_r fmt (l, r) =
  fprintf fmt "%a == %a"
    pp_l l
    pp_r r

let pp_different pp_l pp_r fmt (l, r) =
  fprintf fmt "%a != %a"
    pp_l l
    pp_r r

let pp_implies pp_l pp_r fmt (l, r) =
  fprintf fmt "@[<v>%a ==>@ %a@]"
    pp_l l
    pp_r r

let pp_and pp_l pp_r fmt (l, r) =
  fprintf fmt "@[<v>%a @ && %a@]"
    pp_l l
    pp_r r

let pp_and_l pp_v fmt =
  pp_print_list
    ~pp_open_box:pp_open_vbox0
    ~pp_sep:(fun fmt () -> fprintf fmt "@,&& ")
    pp_v
    fmt

let pp_or pp_l pp_r fmt (l, r) =
  fprintf fmt "@[<v>%a @ || %a@]"
    pp_l l
    pp_r r

let pp_or_l pp_v fmt =
  pp_print_list
    ~pp_open_box:pp_open_vbox0
    ~pp_sep:(fun fmt () -> fprintf fmt "@,|| ")
    pp_v
    fmt

let pp_not pp fmt =
  fprintf fmt "!%a" pp

let pp_valid pp =
  pp_and_l
  (* pp_print_list *)
    (* ~pp_sep:pp_print_cut *)
    (fun fmt x -> fprintf fmt "\\valid(%a)" pp x)

let pp_old pp fmt =
  fprintf fmt "\\old(%a)" pp

let pp_ite pp_c pp_t pp_f fmt (c, t, f) =
  fprintf fmt "(%a @[<hov>? %a@ : %a)@]"
    pp_c c
    pp_t t
    pp_f f

let pp_paren pp fmt v =
  fprintf fmt "(%a)" pp v

let pp_initialization pp_mem fmt (name, mem) =
  fprintf fmt "%s_initialization(%a)" name pp_mem mem

let pp_initialization' = pp_initialization pp_print_string

let pp_locals m =
  pp_comma_list
    ~pp_open_box:pp_open_hbox
    (pp_c_decl_local_var ~pp_c_basic_type_desc:pp_acsl_basic_type_desc m)

let pp_ptr_decl fmt v =
  pp_ptr fmt v.var_id

let pp_basic_assign_spec pp_l pp_r fmt typ var_name value =
  if Types.is_real_type typ && !Options.mpfr
  then
    assert false
    (* Mpfr.pp_inject_assign pp_var fmt (var_name, value) *)
  else
    pp_equal pp_l pp_r fmt (var_name, value)

let pp_assign_spec m self_l pp_var_l indirect_l self_r pp_var_r indirect_r fmt
    (var_type, var_name, value) =
  let depth = expansion_depth value in
  let loop_vars = mk_loop_variables m var_type depth in
  let reordered_loop_vars = reorder_loop_variables loop_vars in
  let rec aux typ fmt vars =
    match vars with
    | [] ->
      pp_basic_assign_spec
        (pp_value_suffix ~indirect:indirect_l m self_l var_type loop_vars pp_var_l)
        (pp_value_suffix ~indirect:indirect_r m self_r var_type loop_vars pp_var_r)
        fmt typ var_name value
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
    | _ -> assert false
  in
  begin
    reset_loop_counter ();
    aux var_type fmt reordered_loop_vars;
  end

let pp_c_var_read m fmt id =
  (* mpfr_t is a static array, not treated as general arrays *)
  if Types.is_address_type id.var_type
  then
    if is_memory m id
    && not (Types.is_real_type id.var_type && !Options.mpfr)
    then fprintf fmt "(*%s)" id.var_id
    else fprintf fmt "%s" id.var_id
  else
    fprintf fmt "%s" id.var_id

let pp_nothing fmt () =
  pp_print_string fmt "\\nothing"

let pp_memory_pack_aux ?i pp_mem pp_self fmt (name, mem, self) =
  fprintf fmt "%s_pack%a(@[<hov>%a,@ %a@])"
    name
    (pp_print_option pp_print_int) i
    pp_mem mem
    pp_self self

let pp_memory_pack pp_mem pp_self fmt (mp, mem, self) =
  pp_memory_pack_aux ?i:mp.mpindex pp_mem pp_self fmt
    (mp.mpname.node_id, mem, self)

let pp_memory_pack_aux' ?i fmt =
  pp_memory_pack_aux ?i pp_print_string pp_print_string fmt
let pp_memory_pack' fmt =
  pp_memory_pack pp_print_string pp_print_string fmt

let pp_transition_aux ?i m pp_mem_in pp_mem_out pp_input pp_output fmt
    (name, inputs, locals, outputs, mem_in, mem_out) =
  let stateless = fst (get_stateless_status m) in
  fprintf fmt "%s_transition%a(@[<hov>%t%a%a%t%a@])"
    name
    (pp_print_option pp_print_int) i
    (fun fmt -> if not stateless then fprintf fmt "%a,@ " pp_mem_in mem_in)
    (pp_comma_list pp_input) inputs
    (pp_print_option (fun fmt _ ->
         pp_comma_list ~pp_prologue:pp_print_comma pp_input fmt locals))
    i
    (fun fmt -> if not stateless then fprintf fmt ",@ %a" pp_mem_out mem_out)
    (pp_comma_list ~pp_prologue:pp_print_comma pp_output) outputs

let pp_transition m pp_mem_in pp_mem_out pp_input pp_output fmt
    (t, mem_in, mem_out) =
  pp_transition_aux ?i:t.tindex m pp_mem_in pp_mem_out pp_input pp_output fmt
    (t.tname.node_id, t.tinputs, t.tlocals, t.toutputs, mem_in, mem_out)

let pp_transition_aux' ?i m =
  pp_transition_aux ?i m pp_print_string pp_print_string pp_var_decl pp_var_decl
let pp_transition_aux'' ?i m =
  pp_transition_aux ?i m pp_print_string pp_print_string pp_var_decl pp_ptr_decl
let pp_transition' m =
  pp_transition m pp_print_string pp_print_string pp_var_decl pp_var_decl
let pp_transition'' m =
  pp_transition m pp_print_string pp_print_string pp_var_decl pp_ptr_decl

let pp_reset_cleared pp_mem_in pp_mem_out fmt (name, mem_in, mem_out) =
  fprintf fmt "%s_reset_cleared(@[<hov>%a,@ %a@])"
    name
    pp_mem_in mem_in
    pp_mem_out mem_out

let pp_reset_cleared' = pp_reset_cleared pp_print_string pp_print_string

module PrintSpec = struct

  let pp_reg pp_mem fmt = function
    | ResetFlag ->
      fprintf fmt "%t_reset" pp_mem
    | StateVar x ->
      fprintf fmt "%t%a" pp_mem pp_var_decl x

  let pp_expr:
    type a. machine_t -> (formatter -> unit) -> formatter -> (value_t, a) expression_t -> unit =
    fun m pp_mem fmt -> function
    | Val v -> pp_val m fmt v
    | Tag t -> pp_print_string fmt t
    | Var v -> pp_var_decl fmt v
    | Memory r -> pp_reg pp_mem fmt r

  let pp_predicate m mem_in mem_in' mem_out mem_out' fmt p =
    let pp_expr: type a. formatter -> (value_t, a) expression_t -> unit =
      fun fmt e -> pp_expr m (fun fmt -> fprintf fmt "%s." mem_out) fmt e
    in
    match p with
    | Transition (f, inst, i, inputs, locals, outputs) ->
      let pp_mem_in, pp_mem_out = match inst with
        | None ->
          pp_print_string, pp_print_string
        | Some inst ->
          (fun fmt mem_in -> pp_access' fmt (mem_in, inst)),
          (fun fmt mem_out -> pp_access' fmt (mem_out, inst))
      in
      pp_transition_aux ?i m pp_mem_in pp_mem_out pp_expr pp_expr fmt
        (f, inputs, locals, outputs, mem_in', mem_out')
    | MemoryPack (f, inst, i) ->
      let pp_mem, pp_self = match inst with
        | None ->
          pp_print_string, pp_print_string
        | Some inst ->
          (fun fmt mem -> pp_access' fmt (mem, inst)),
          (fun fmt self -> pp_indirect' fmt (self, inst))
      in
      pp_memory_pack_aux ?i pp_mem pp_self fmt (f, mem_out, mem_in)
    | ResetCleared f ->
      pp_reset_cleared' fmt (f, mem_in, mem_out)
      (* fprintf fmt "ResetCleared_%a" pp_print_string f *)
    | Initialization -> ()

  let reset_flag = dummy_var_decl "_reset" Type_predef.type_bool

  let val_of_expr: type a. (value_t, a) expression_t -> value_t = function
    | Val v -> v
    | Tag t -> id_to_tag t
    | Var v -> vdecl_to_val v
    | Memory (StateVar v) -> vdecl_to_val v
    | Memory ResetFlag -> vdecl_to_val reset_flag

  type mode =
    | MemoryPackMode
    | TransitionMode
    | ResetIn
    | ResetOut
    | InstrMode of ident

  let find_arrow m =
    try
      List.find (fun (_, (td, _)) -> Arrow.td_is_arrow td) m.minstances
      |> fst
    with Not_found -> eprintf "Internal error: arrow not found"; raise Not_found

  let pp_spec mode m =
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
        | ResetIn ->
          mem_in, mem_in, false, mem_reset, mem_reset, false
        | ResetOut ->
          mem_reset, mem_reset, false, mem_out, mem_out, false
        | InstrMode self ->
          let mem = "*" ^ mem in
          fprintf str_formatter "%a" (pp_at pp_print_string) (mem, reset_label);
          self, flush_str_formatter (), false,
          mem, mem, false
      in
      let pp_expr: type a. formatter -> (value_t, a) expression_t -> unit =
        fun fmt e -> pp_expr m (fun fmt -> fprintf fmt "%s." mem_out) fmt e
      in
      let pp_spec' = pp_spec mode in
      match f with
      | True ->
        pp_true fmt ()
      | False ->
        pp_false fmt ()
      | Equal (a, b) ->
        pp_assign_spec m
          mem_out (pp_c_var_read m) indirect_l
          mem_in (pp_c_var_read m) indirect_r
          fmt
          (type_of_l_value a, val_of_expr a, val_of_expr b)
      | And fs ->
        pp_and_l pp_spec' fmt fs
      | Or fs ->
        pp_or_l pp_spec' fmt fs
      | Imply (a, b) ->
        pp_par (pp_implies pp_spec' pp_spec') fmt (a, b)
      | Exists (xs, a) ->
        pp_exists (pp_locals m) pp_spec' fmt (xs, a)
      | Forall (xs, a) ->
        pp_forall (pp_locals m) pp_spec' fmt (xs, a)
      | Ternary (e, a, b) ->
        pp_ite pp_expr pp_spec' pp_spec' fmt (e, a, b)
      | Predicate p ->
        pp_predicate m mem_in mem_in' mem_out mem_out' fmt p
      | StateVarPack ResetFlag ->
        let r = vdecl_to_val reset_flag in
        pp_assign_spec m
          mem_out (pp_c_var_read m) indirect_l
          mem_in (pp_c_var_read m) indirect_r
          fmt
          (Type_predef.type_bool, r, r)
      | StateVarPack (StateVar v) ->
        let v' = vdecl_to_val v in
        let inst = find_arrow m in
        pp_par (pp_implies
                  (pp_not (pp_initialization pp_access'))
                  (pp_assign_spec m
                     mem_out (pp_c_var_read m) indirect_l
                     mem_in (pp_c_var_read m) indirect_r))
          fmt
          ((Arrow.arrow_id, (mem_out, inst)),
           (v.var_type, v', v'))
      | ExistsMem (rc, tr) ->
        pp_exists
          (pp_machine_decl' ~ghost:true)
          (pp_and (pp_spec ResetIn) (pp_spec ResetOut))
          fmt
          ((m.mname.node_id, mk_mem_reset m),
           (rc, tr))
          (* fprintf fmt "@[<hv 2>∃ MEM,@ %a@]" pp_spec f *)
    in
    pp_spec mode

end

let pp_predicate pp_l pp_r fmt (l, r) =
  fprintf fmt "@[<v 2>predicate %a =@,%a;@]"
    pp_l l
    pp_r r

let print_machine_valid_predicate fmt m =
  if not (fst (get_stateless_status m)) then
    let name = m.mname.node_id in
    let self = mk_self m in
    pp_acsl
      (pp_predicate
         (pp_mem_valid (pp_machine_decl pp_ptr))
         (pp_and
            (pp_and_l (fun fmt (_, (td, _) as inst) ->
                 pp_mem_valid (pp_inst self) fmt (node_name td, inst)))
            (pp_valid pp_print_string)))
      fmt
      ((name, (name, self)),
       (m.minstances, [self]))


let pp_memory_pack_def m fmt mp =
  let name = mp.mpname.node_id in
  let self = mk_self m in
  let mem = mk_mem m in
  pp_acsl
    (pp_predicate
       (pp_memory_pack (pp_machine_decl' ~ghost:true) (pp_machine_decl pp_ptr))
       (PrintSpec.pp_spec MemoryPackMode m))
    fmt
    ((mp, (name, mem), (name, self)),
     mp.mpformula)

let print_machine_ghost_struct fmt m =
  pp_acsl (pp_ghost (print_machine_struct ~ghost:true)) fmt m

let pp_memory_pack_defs fmt m =
  if not (fst (get_stateless_status m)) then
    fprintf fmt "%a@,%a"
      print_machine_ghost_struct m
      (pp_print_list
         ~pp_epilogue:pp_print_cut
         ~pp_open_box:pp_open_vbox0
         (pp_memory_pack_def m)) m.mspec.mmemory_packs

let pp_transition_def m fmt t =
  let name = t.tname.node_id in
  let mem_in = mk_mem_in m in
  let mem_out = mk_mem_out m in
  pp_acsl
    (pp_predicate
       (pp_transition m
          (pp_machine_decl' ~ghost:true) (pp_machine_decl' ~ghost:true)
          (pp_c_decl_local_var ~pp_c_basic_type_desc:pp_acsl_basic_type_desc m)
          (pp_c_decl_local_var ~pp_c_basic_type_desc:pp_acsl_basic_type_desc m))
       (PrintSpec.pp_spec TransitionMode m))
    fmt
    ((t, (name, mem_in), (name, mem_out)),
     t.tformula)

(* let print_trans_simulation dependencies m fmt (i, instr) =
 *   let mem_in = mk_mem_in m in
 *   let mem_out = mk_mem_out m in
 *   let d = VDSet.(diff (union (live_i m i) (assigned empty instr))
 *                    (live_i m (i+1))) in
 *   (\* XXX *\)
 *   (\* printf "%d : %a\n%d : %a\nocc: %a\n\n"
 *    *   i
 *    *   (pp_print_parenthesized pp_var_decl) (VDSet.elements (live_i m i))
 *    *   (i+1)
 *    *   (pp_print_parenthesized pp_var_decl) (VDSet.elements (live_i m (i+1)))
 *    *   (pp_print_parenthesized pp_var_decl) VDSet.(elements (assigned empty instr)); *\)
 *   let prev_trans fmt () = pp_mem_trans' ~i fmt (m, mem_in, mem_out) in
 *   let pred pp v =
 *     let vars = VDSet.(union (of_list m.mstep.step_locals)
 *                         (of_list m.mstep.step_outputs)) in
 *     let locals = VDSet.(inter vars d |> elements) in
 *     if locals = []
 *     then pp_and prev_trans pp fmt ((), v)
 *     else pp_exists (pp_locals m) (pp_and prev_trans pp) fmt (locals, ((), v))
 *   in
 *   let rec aux fmt instr = match instr.instr_desc with
 *     | MLocalAssign (x, v)
 *     | MStateAssign (x, v) ->
 *       pp_assign_spec m mem_out (pp_c_var_read m) mem_in (pp_c_var_read m) fmt
 *         (x.var_type, mk_val (Var x) x.var_type, v)
 *     | MStep ([i0], i, vl)
 *       when Basic_library.is_value_internal_fun
 *           (mk_val (Fun (i, vl)) i0.var_type)  ->
 *       pp_true fmt ()
 *     | MStep (_, i, _) when !Options.mpfr && Mpfr.is_homomorphic_fun i ->
 *       pp_true fmt ()
 *     | MStep ([_], i, _) when has_c_prototype i dependencies ->
 *       pp_true fmt ()
 *     | MStep (xs, i, ys) ->
 *       begin try
 *           let n, _ = List.assoc i m.minstances in
 *           pp_mem_trans_aux
 *             (fst (get_stateless_status_top_decl n))
 *             pp_access' pp_access'
 *             (pp_c_val m mem_in (pp_c_var_read m))
 *             pp_var_decl
 *             fmt
 *             (node_name n, ys, [], xs, (mem_in, i), (mem_out, i))
 *         with Not_found -> pp_true fmt ()
 *       end
 *     | MReset i ->
 *       begin try
 *           let n, _ = List.assoc i m.minstances in
 *           pp_mem_init' fmt (node_name n, mem_out)
 *         with Not_found -> pp_true fmt ()
 *       end
 *     | MBranch (v, brs) ->
 *       if let t = fst (List.hd brs) in t = tag_true || t = tag_false
 *       then (\* boolean case *\)
 *         pp_ite (pp_c_val m mem_in (pp_c_var_read m))
 *           (fun fmt () ->
 *              match List.assoc tag_true brs with
 *              | _ :: _ as l -> pp_paren (pp_and_l aux) fmt l
 *              | []
 *              | exception Not_found -> pp_true fmt ())
 *           (fun fmt () ->
 *              match List.assoc tag_false brs with
 *              | _ :: _ as l -> pp_paren (pp_and_l aux) fmt l
 *              | []
 *              | exception Not_found -> pp_true fmt ())
 *           fmt (v, (), ())
 *       else (\* enum type case *\)
 *       pp_and_l (fun fmt (l, instrs) ->
 *             let pp_val = pp_c_val m mem_in (pp_c_var_read m) in
 *             pp_paren (pp_implies
 *                         (pp_equal pp_val pp_c_tag)
 *                         (pp_and_l aux))
 *               fmt
 *               ((v, l), instrs))
 *         fmt brs
 *     | _ -> pp_true fmt ()
 *   in
 *   pred aux instr *)

(* let print_machine_trans_simulation dependencies m fmt i instr =
 *   print_machine_trans_simulation_aux m
 *     (print_trans_simulation dependencies m)
 *     ~i:(i+1)
 *     fmt (i, instr) *)

let pp_transition_defs fmt m =
  (* set_live_of m; *)
  (* let i = List.length m.mstep.step_instrs in *)
  (* let mem_in = mk_mem_in m in
   * let mem_out = mk_mem_out m in *)
  (* let last_trans fmt () =
   *   let locals = VDSet.(inter
   *                         (of_list m.mstep.step_locals)
   *                         (live_i m i)
   *                       |> elements) in
   *   if locals = []
   *   then pp_mem_trans' ~i fmt (m, mem_in, mem_out)
   *   else pp_exists (pp_locals m) (pp_mem_trans' ~i) fmt
   *       (locals, (m, mem_in, mem_out))
   * in *)
  fprintf fmt "%a"
    (pp_print_list
       ~pp_epilogue:pp_print_cut
       ~pp_open_box:pp_open_vbox0
       (pp_transition_def m)) m.mspec.mtransitions

let print_machine_init_predicate fmt m =
  if not (fst (get_stateless_status m)) then
    let name = m.mname.node_id in
    let mem_in = mk_mem_in m in
    pp_acsl
      (pp_predicate
         (pp_initialization (pp_machine_decl' ~ghost:true))
         (pp_and_l (fun fmt (i, (td, _)) ->
              pp_initialization pp_access' fmt (node_name td, (mem_in, i)))))
      fmt
      ((name, (name, mem_in)), m.minstances)

let pp_at pp_p fmt (p, l) =
  fprintf fmt "\\at(%a, %s)" pp_p p l

let label_pre = "Pre"

let pp_at_pre pp_p fmt p =
  pp_at pp_p fmt (p, label_pre)

let pp_register ?(indirect=true) ptr =
  pp_print_list
    ~pp_prologue:(fun fmt () -> fprintf fmt "%s->" ptr)
    ~pp_epilogue:(fun fmt () -> fprintf fmt "%s_reg._first"
                     (if indirect then "->" else "."))
    ~pp_sep:(fun fmt () -> pp_print_string fmt (if indirect then "->" else "."))
    (fun fmt (i, _) -> pp_print_string fmt i)

let pp_reset_flag ?(indirect=true) ptr fmt mems =
  pp_print_list
    ~pp_prologue:(fun fmt () -> fprintf fmt "%s->" ptr)
    ~pp_epilogue:(fun fmt () -> fprintf fmt "%s_reset"
                     (if indirect then "->" else "."))
    ~pp_sep:(fun fmt () -> pp_print_string fmt (if indirect then "->" else "."))
    (fun fmt (i, _) -> pp_print_string fmt i)
    fmt mems

module GhostProto: MODIFIERS_GHOST_PROTO = struct
  let pp_ghost_parameters fmt vs =
    fprintf fmt "@;%a"
      (pp_acsl (pp_ghost (pp_print_parenthesized (fun fmt (x, pp) -> pp fmt x))))
      vs
end

module HdrMod = struct

  module GhostProto = GhostProto

  let print_machine_decl_prefix = fun _ _ -> ()

  let pp_import_standard_spec fmt () =
    fprintf fmt "@,#include \"%s/arrow_spec.h%s\""
      (Arrow.arrow_top_decl ()).top_decl_owner
      (if !Options.cpp then "pp" else "")

end

module SrcMod = struct

  module GhostProto = GhostProto

  let pp_predicates (* dependencies *) fmt machines =
    fprintf fmt
      "%a%a%a%a"
      (pp_print_list
         ~pp_open_box:pp_open_vbox0
         ~pp_prologue:(pp_print_endcut "/* ACSL `valid` predicates */")
         print_machine_valid_predicate
         ~pp_epilogue:pp_print_cutcut) machines
      (pp_print_list
         ~pp_open_box:pp_open_vbox0
         ~pp_sep:pp_print_cutcut
         ~pp_prologue:(pp_print_endcut "/* ACSL ghost simulations */")
         pp_memory_pack_defs
         ~pp_epilogue:pp_print_cutcut) machines
      (pp_print_list
         ~pp_open_box:pp_open_vbox0
         ~pp_sep:pp_print_cutcut
         ~pp_prologue:(pp_print_endcut "/* ACSL initialization annotations */")
         print_machine_init_predicate
         ~pp_epilogue:pp_print_cutcut) machines
      (pp_print_list
         ~pp_open_box:pp_open_vbox0
         ~pp_sep:pp_print_cutcut
         ~pp_prologue:(pp_print_endcut "/* ACSL transition annotations */")
         pp_transition_defs
         ~pp_epilogue:pp_print_cutcut) machines

  let pp_clear_reset_spec fmt machines self mem m =
    let name = m.mname.node_id in
    let arws, narws = List.partition (fun (_, (td, _)) -> Arrow.td_is_arrow td)
        m.minstances in
    let mk_insts = List.map (fun x -> [x]) in
    pp_acsl_cut (fun fmt () ->
        fprintf fmt
          "%a@,%a@,%a@,%a@,%a@,%a@,%a@,%a@,%a@,\
          @[<v 2>behavior reset:@;\
          %a@,%a@]@,\
          @[<v 2>behavior no_reset:@;\
          %a@,%a@]"
          (pp_requires pp_mem_valid') (name, self)
          (pp_requires (pp_separated self mem)) (mk_insts m.minstances, [])
          (pp_ensures (pp_memory_pack_aux
                         ~i:(List.length m.mspec.mmemory_packs - 2)
                         pp_ptr pp_print_string))
          (name, mem, self)
          (pp_assigns pp_indirect') [self, "_reset"]
          (pp_assigns (pp_register self)) (mk_insts arws)
          (pp_assigns (pp_reset_flag self)) (mk_insts narws)
          (pp_assigns pp_indirect') [mem, "_reset"]
          (pp_assigns (pp_register ~indirect:false mem)) (mk_insts arws)
          (pp_assigns (pp_reset_flag ~indirect:false mem)) (mk_insts narws)
          (pp_assumes (pp_equal pp_indirect' pp_print_int)) ((mem, "_reset"), 1)
          (pp_ensures (pp_initialization pp_ptr)) (name, mem)
          (pp_assumes (pp_equal pp_indirect' pp_print_int)) ((mem, "_reset"), 0)
          (pp_ensures (pp_equal pp_ptr (pp_old pp_ptr))) (mem, mem)
      )
      fmt ()

  let pp_set_reset_spec fmt self mem m =
    let name = m.mname.node_id in
    pp_acsl_cut (fun fmt () ->
        fprintf fmt
          "%a@,%a@,%a"
          (pp_ensures (pp_memory_pack_aux pp_ptr pp_print_string)) (name, mem, self)
          (pp_ensures (pp_equal pp_indirect' pp_print_string)) ((mem, "_reset"), "1")
          (pp_assigns (fun fmt ptr -> pp_indirect' fmt (ptr, "_reset"))) [self; mem])
      fmt ()

  let pp_step_spec fmt machines self mem m =
    let name = m.mname.node_id in
    let insts = instances machines m in
    let insts' = powerset_instances insts in
    let insts'' = List.(filter (fun l -> l <> [])
                          (map (filter (fun (_, (td, _)) ->
                               not (Arrow.td_is_arrow td))) insts)) in
    let inputs = m.mstep.step_inputs in
    let outputs = m.mstep.step_outputs in
    pp_acsl_cut (fun fmt () ->
        if fst (get_stateless_status m) then
          fprintf fmt
            "%a@,%a@,%a@,%a"
            (pp_requires (pp_valid pp_var_decl)) outputs
            (pp_requires pp_separated') outputs
            (pp_assigns pp_ptr_decl) outputs
            (pp_ensures (pp_transition_aux'' m))
            (name, inputs, [], outputs, "", "")
        else
          fprintf fmt
            "%a@,%a@,%a@,%a@,%a@,%a@,%a@,%a@,%a@,%a@,%a@,%a@,%a@,%a"
            (pp_requires (pp_valid pp_var_decl)) outputs
            (pp_requires pp_mem_valid') (name, self)
            (pp_requires (pp_separated self mem)) (insts', outputs)
            (pp_requires (pp_memory_pack_aux pp_ptr pp_print_string))
            (name, mem, self)
            (pp_assigns pp_ptr_decl) outputs
            (pp_assigns (pp_reg self)) m.mmemory
            (pp_assigns (pp_memory self)) (memories insts')
            (pp_assigns (pp_register self)) insts
            (pp_assigns (pp_reset_flag self)) insts''
            (pp_assigns (pp_reg mem)) m.mmemory
            (pp_assigns (pp_memory ~indirect:false mem)) (memories insts')
            (pp_assigns (pp_register ~indirect:false mem)) insts
            (pp_assigns (pp_reset_flag ~indirect:false mem)) insts''
            (pp_ensures (pp_transition_aux m (pp_old pp_ptr)
                           pp_ptr pp_var_decl pp_ptr_decl))
            (name, inputs, [], outputs, mem, mem)
      )
      fmt ()

  let pp_step_instr_spec m self fmt instr =
    fprintf fmt "@,%a"
      (pp_print_list ~pp_open_box:pp_open_vbox0
         (pp_acsl (pp_assert (PrintSpec.pp_spec (InstrMode self) m))))
      instr.instr_spec

  let pp_ghost_set_reset_spec fmt =
    fprintf fmt "@;%a@;"
      (pp_acsl_line
         (pp_ghost
            (fun fmt mem -> fprintf fmt "%a = 1;" pp_indirect' (mem, "_reset"))))
end

(**************************************************************************)
(*                              MAKEFILE                                  *)
(**************************************************************************)

module MakefileMod = struct

  let other_targets fmt basename _nodename dependencies =
    fprintf fmt "FRAMACEACSL=`frama-c -print-share-path`/e-acsl@.";
    (* EACSL version of library file . c *)
    fprintf fmt "%s_eacsl.c: %s.c %s.h@." basename basename basename;
    fprintf fmt
      "\tframa-c -e-acsl-full-mmodel -machdep x86_64 -e-acsl %s.c -then-on e-acsl -print -ocode %s_eacsl.c@."
      basename basename;
    fprintf fmt "@.";
    fprintf fmt "@.";

    (* EACSL version of library file . c + main .c  *)
    fprintf fmt "%s_main_eacsl.c: %s.c %s.h %s_main.c@." basename basename basename basename;
    fprintf fmt "\tframa-c -e-acsl-full-mmodel -machdep x86_64 -e-acsl %s.c %s_main.c -then-on e-acsl -print -ocode %s_main_eacsl.i@."
      basename basename basename;
    (* Ugly hack to deal with eacsl bugs *)
    fprintf fmt "\tgrep -v _fc_stdout %s_main_eacsl.i > %s_main_eacsl.c" basename basename;
    fprintf fmt "@.";
    fprintf fmt "@.";

    (* EACSL version of binary *)
    fprintf fmt "%s_main_eacsl: %s_main_eacsl.c@." basename basename;
    fprintf fmt "\t${GCC} -Wno-attributes -I${INC} -I. -c %s_main_eacsl.c@." basename; (* compiling instrumented lib + main *)
    C_backend_makefile.fprintf_dependencies fmt dependencies;
    fprintf fmt "\t${GCC} -Wno-attributes -o %s_main_eacsl io_frontend.o %a %s %s_main_eacsl.o %a@."
      basename
      (Utils.fprintf_list ~sep:" " (fun fmt dep -> Format.fprintf fmt "%s.o" dep.name))
      (C_backend_makefile.compiled_dependencies dependencies)
      ("${FRAMACEACSL}/e_acsl.c "
       ^ "${FRAMACEACSL}/memory_model/e_acsl_bittree.c "
       ^ "${FRAMACEACSL}/memory_model/e_acsl_mmodel.c")
      basename
      (Utils.fprintf_list ~sep:" " (fun fmt lib -> fprintf fmt "-l%s" lib))
      (C_backend_makefile.lib_dependencies dependencies)
    ;
    fprintf fmt "@."

end

(* Local Variables: *)
(* compile-command:"make -C ../../.." *)
(* End: *)
