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
open Machine_code_common
open Corelang

(**************************************************************************)
(*     Printing spec for c *)

(**************************************************************************)
(* OLD STUFF ???


let pp_acsl_type var fmt t =
  let rec aux t pp_suffix =
  match (Types.repr t).Types.tdesc with
  | Types.Tclock t'       -> aux t' pp_suffix
  | Types.Tbool           -> fprintf fmt "int %s%a" var pp_suffix ()
  | Types.Treal           -> fprintf fmt "real %s%a" var pp_suffix ()
  | Types.Tint            -> fprintf fmt "int %s%a" var pp_suffix ()
  | Types.Tarray (d, t')  ->
    let pp_suffix' fmt () = fprintf fmt "%a[%a]" pp_suffix () pp_c_dimension d in
    aux t' pp_suffix'
  (* | Types.Tstatic (_, t') -> fprintf fmt "const "; aux t' pp_suffix *)
  (* | Types.Tconst ty       -> fprintf fmt "%s %s" ty var *)
  (* | Types.Tarrow (_, _)   -> fprintf fmt "void (\*%s)()" var *)
  | _                     -> eprintf "internal error: pp_acsl_type %a@." Types.print_ty t; assert false
  in aux t (fun fmt () -> ())

let pp_acsl_var_decl fmt id =
  pp_acsl_type id.var_id fmt id.var_type


let rec pp_eexpr is_output fmt eexpr = 
  let pp_eexpr = pp_eexpr is_output in
  match eexpr.eexpr_desc with
    | EExpr_const c -> Printers.pp_econst fmt c
    | EExpr_ident id -> 
      if is_output id then pp_print_string fmt ("*" ^ id) else pp_print_string fmt id
    | EExpr_tuple el -> Utils.fprintf_list ~sep:"," pp_eexpr fmt el
    | EExpr_arrow (e1, e2) -> fprintf fmt "%a -> %a" pp_eexpr e1 pp_eexpr e2
    | EExpr_fby (e1, e2) -> fprintf fmt "%a fby %a" pp_eexpr e1 pp_eexpr e2
    (* | EExpr_concat (e1, e2) -> fprintf fmt "%a::%a" pp_eexpr e1 pp_eexpr e2 *)
    (* | EExpr_tail e -> fprintf fmt "tail %a" pp_eexpr e *)
    | EExpr_pre e -> fprintf fmt "pre %a" pp_eexpr e
    | EExpr_when (e, id) -> fprintf fmt "%a when %s" pp_eexpr e id
    | EExpr_merge (id, e1, e2) -> 
      fprintf fmt "merge (%s, %a, %a)" id pp_eexpr e1 pp_eexpr e2
    | EExpr_appl (id, e, r) -> pp_eapp is_output fmt id e r
    | EExpr_forall (vars, e) -> fprintf fmt "forall %a; %a" Printers.pp_node_args vars pp_eexpr e 
    | EExpr_exists (vars, e) -> fprintf fmt "exists %a; %a" Printers.pp_node_args vars pp_eexpr e 


    (* | EExpr_whennot _ *)
    (* | EExpr_uclock _ *)
    (* | EExpr_dclock _ *)
    (* | EExpr_phclock _ -> assert false *)
and pp_eapp is_output fmt id e r =
  let pp_eexpr = pp_eexpr is_output in
  match r with
  | None ->
    (match id, e.eexpr_desc with
    | "+", EExpr_tuple([e1;e2]) -> fprintf fmt "(%a + %a)" pp_eexpr e1 pp_eexpr e2
    | "uminus", _ -> fprintf fmt "(- %a)" pp_eexpr e
    | "-", EExpr_tuple([e1;e2]) -> fprintf fmt "(%a - %a)" pp_eexpr e1 pp_eexpr e2
    | "*", EExpr_tuple([e1;e2]) -> fprintf fmt "(%a * %a)" pp_eexpr e1 pp_eexpr e2
    | "/", EExpr_tuple([e1;e2]) -> fprintf fmt "(%a / %a)" pp_eexpr e1 pp_eexpr e2
    | "mod", EExpr_tuple([e1;e2]) -> fprintf fmt "(%a mod %a)" pp_eexpr e1 pp_eexpr e2
    | "&&", EExpr_tuple([e1;e2]) -> fprintf fmt "(%a && %a)" pp_eexpr e1 pp_eexpr e2
    | "||", EExpr_tuple([e1;e2]) -> fprintf fmt "(%a || %a)" pp_eexpr e1 pp_eexpr e2
    | "xor", EExpr_tuple([e1;e2]) -> fprintf fmt "(%a ^^ %a)" pp_eexpr e1 pp_eexpr e2
    | "impl", EExpr_tuple([e1;e2]) -> fprintf fmt "(%a ==> %a)" pp_eexpr e1 pp_eexpr e2
    | "<", EExpr_tuple([e1;e2]) -> fprintf fmt "(%a < %a)" pp_eexpr e1 pp_eexpr e2
    | "<=", EExpr_tuple([e1;e2]) -> fprintf fmt "(%a <= %a)" pp_eexpr e1 pp_eexpr e2
    | ">", EExpr_tuple([e1;e2]) -> fprintf fmt "(%a > %a)" pp_eexpr e1 pp_eexpr e2
    | ">=", EExpr_tuple([e1;e2]) -> fprintf fmt "(%a >= %a)" pp_eexpr e1 pp_eexpr e2
    | "!=", EExpr_tuple([e1;e2]) -> fprintf fmt "(%a != %a)" pp_eexpr e1 pp_eexpr e2
    | "=", EExpr_tuple([e1;e2]) -> fprintf fmt "(%a == %a)" pp_eexpr e1 pp_eexpr e2
    | "not", _ -> fprintf fmt "(! %a)" pp_eexpr e
    | "ite", EExpr_tuple([e1;e2;e3]) -> fprintf fmt "(if %a then %a else %a)" pp_eexpr e1 pp_eexpr e2 pp_eexpr e3
    | _ -> fprintf fmt "%s (%a)" id pp_eexpr e)
  | Some x -> fprintf fmt "%s (%a) every %s" id pp_eexpr e x 

let pp_ensures is_output fmt e =
  match e with
    | EnsuresExpr e -> fprintf fmt "ensures %a;@ " (pp_eexpr is_output) e
    | SpecObserverNode (name, args) -> fprintf fmt "observer %s (%a);@ " name (Utils.fprintf_list ~sep:", " (pp_eexpr is_output)) args

let pp_acsl_spec outputs fmt spec =
  let is_output = fun oid -> List.exists (fun v -> v.var_id = oid) outputs in
  let pp_eexpr = pp_eexpr is_output in
  fprintf fmt "@[<v 2>/*@@ ";
  Utils.fprintf_list ~sep:"" (fun fmt r -> fprintf fmt "requires %a;@ " pp_eexpr r) fmt spec.requires;
  Utils.fprintf_list ~sep:"" (pp_ensures is_output) fmt spec.ensures;
  fprintf fmt "@ ";
  (* fprintf fmt "assigns *self%t%a;@ "  *)
  (*   (fun fmt -> if List.length outputs > 0 then fprintf fmt ", ") *)
  (*   (fprintf_list ~sep:"," (fun fmt v -> fprintf fmt "*%s" v.var_id)) outputs; *)
  Utils.fprintf_list ~sep:"@ " (fun fmt (name, assumes, requires) -> 
    fprintf fmt "behavior %s:@[@ %a@ %a@]" 
      name
      (Utils.fprintf_list ~sep:"@ " (fun fmt r -> fprintf fmt "assumes %a;" pp_eexpr r)) assumes
      (Utils.fprintf_list ~sep:"@ " (pp_ensures is_output)) requires
  ) fmt spec.behaviors;
  fprintf fmt "@]@ */@.";
  ()




let print_machine_decl_prefix fmt m =
   (* Print specification if any *)
   (match m.mspec with
  | None -> ()
  | Some spec -> 
    pp_acsl_spec m.mstep.step_outputs fmt spec
  )

  *)

   (* TODO ACSL
   Return updates machines (eg with local annotations) and acsl preamble *)
let preprocess_acsl machines = machines, []
                          
(* TODO: This preamble shall be a list of types, axiomatics, predicates, theorems *)
let pp_acsl_preamble fmt _preamble =
  Format.fprintf fmt "";
  ()

let pp_spec pp fmt =
  fprintf fmt "@[<v>/*%@@[<v>@,%a@]@,*/@]" pp

let pp_spec_cut pp fmt =
  fprintf fmt "%a@," (pp_spec pp)

let pp_spec_line pp fmt =
  fprintf fmt "//%@ %a@," pp

let pp_requires pp_req fmt =
  fprintf fmt "requires %a;" pp_req

let pp_ensures pp_ens fmt =
  fprintf fmt "ensures %a;" pp_ens

let pp_assigns pp_asg fmt =
  fprintf fmt "assigns %a;" pp_asg

let pp_ghost pp_gho fmt =
  fprintf fmt "ghost %a" pp_gho

let pp_assert pp_ast fmt =
  fprintf fmt "assert %a;" pp_ast

let pp_mem_valid pp_var fmt (name, var) =
  fprintf fmt "%s_valid(%a)" name pp_var var

let pp_mem_valid' = pp_mem_valid pp_print_string

let pp_indirect pp_field fmt (ptr, field) =
  fprintf fmt "%s->%a" ptr pp_field field

let pp_indirect' = pp_indirect pp_print_string

let pp_access pp_field fmt (stru, field) =
  fprintf fmt "%s.%a" stru pp_field field

let pp_access' = pp_access pp_print_string

let pp_inst self fmt (name, _) =
  pp_indirect' fmt (self, name)

let pp_true fmt () =
  pp_print_string fmt "\\true"

let pp_separated self fmt =
  fprintf fmt "\\separated(@[<h>%s%a@])"
    self
    (pp_print_list
       ~pp_prologue:pp_print_comma
       ~pp_sep:pp_print_comma
       (pp_inst self))

let pp_forall pp_l pp_r fmt (l, r) =
  fprintf fmt "@[<v 2>\\forall %a;@,%a@]"
    pp_l l
    pp_r r

let pp_valid =
  pp_print_parenthesized
    ~pp_nil:pp_true
    ~pp_prologue:(fun fmt () -> pp_print_string fmt "\\valid")

let pp_equal pp_l pp_r fmt (l, r) =
  fprintf fmt "%a == %a"
    pp_l l
    pp_r r

let pp_implies pp_l pp_r fmt (l, r) =
  fprintf fmt "%a ==>@ %a"
    pp_l l
    pp_r r

let pp_and pp_l pp_r fmt (l, r) =
  fprintf fmt "%a @ && %a"
    pp_l l
    pp_r r

let pp_and_l pp_v fmt =
  pp_print_list
    ~pp_open_box:pp_open_vbox0
    ~pp_sep:(fun fmt () -> fprintf fmt "@,&& ")
    pp_v
    fmt

let pp_ite pp_c pp_t pp_f fmt (c, t, f) =
  fprintf fmt "%a @[<hov>? %a@ : %a@]"
    pp_c c
    pp_t t
    pp_f f

let pp_machine_decl fmt (id, mem_type, var) =
  fprintf fmt "struct %s_%s %s" id mem_type var

let pp_mem_ghost pp_mem pp_self ?i fmt (name, mem, self) =
  fprintf fmt "%s_ghost%a(@[<hov>%a,@ %a@])"
    name
    (pp_print_option pp_print_int) i
    pp_mem mem
    pp_self self

let pp_mem_ghost' = pp_mem_ghost pp_print_string pp_print_string

let pp_mem_init pp_mem fmt (name, mem) =
  fprintf fmt "%s_init(%a)" name pp_mem mem

let pp_mem_init' = pp_mem_init pp_print_string

let pp_var_decl fmt v =
  pp_print_string fmt v.var_id

let pp_ptr_decl fmt v =
  fprintf fmt "*%s" v.var_id

let pp_mem_trans_aux ?i pp_mem_in pp_mem_out pp_input pp_output fmt
    (name, inputs, outputs, mem_in, mem_out) =
  fprintf fmt "%s_trans%a(@[<hov>%a,@ %a%a%a@])"
    name
    (pp_print_option pp_print_int) i
    pp_mem_in mem_in
    (pp_print_list
       ~pp_epilogue:pp_print_comma
       ~pp_sep:pp_print_comma
       pp_input) inputs
    pp_mem_out mem_out
    (pp_print_list
       ~pp_prologue:pp_print_comma
       ~pp_sep:pp_print_comma
       pp_output) outputs

let pp_mem_trans ?i pp_mem_in pp_mem_out fmt (m, mem_in, mem_out) =
  pp_mem_trans_aux ?i pp_mem_in pp_mem_out pp_var_decl pp_ptr_decl fmt
    (m.mname.node_id, m.mstep.step_inputs, m.mstep.step_outputs, mem_in, mem_out)

let pp_mem_trans' ?i fmt = pp_mem_trans ?i pp_print_string pp_print_string fmt

let pp_nothing fmt () =
  pp_print_string fmt "\\nothing"

let pp_predicate pp_l pp_r fmt (l, r) =
  fprintf fmt "@[<v 2>predicate %a =@,%a;@]"
    pp_l l
    pp_r r

let print_machine_valid_predicate fmt m =
  if not (fst (Machine_code_common.get_stateless_status m)) then
    let name = m.mname.node_id in
    let self = mk_self m in
    pp_spec
      (pp_predicate
         (pp_mem_valid pp_machine_decl)
         (pp_and
            (pp_and_l (fun fmt (_, (td, _) as inst) ->
                 pp_mem_valid (pp_inst self) fmt (node_name td, inst)))
            (pp_valid pp_print_string)))
      fmt
      ((name, (name, "mem", "*" ^ self)),
       (m.minstances, [self]))

let print_machine_ghost_simulation_aux ?i m pp fmt v =
  let name = m.mname.node_id in
  let self = mk_self m in
  let mem = mk_mem m in
  pp_spec
    (pp_predicate
       (pp_mem_ghost pp_machine_decl pp_machine_decl ?i)
       pp)
    fmt
    ((name, (name, "mem_ghost", mem), (name, "mem", "*" ^ self)),
     v)

let print_machine_ghost_simulation dependencies m fmt i instr =
  let name = m.mname.node_id in
  let self = mk_self m in
  let mem = mk_mem m in
  let prev_ghost fmt () = pp_mem_ghost' ~i fmt (name, mem, self) in
  let pred pp v = pp_and prev_ghost pp fmt ((), v) in
  print_machine_ghost_simulation_aux m
    (fun fmt -> function
       | MStateAssign (m, _) ->
         pred
           (pp_equal
              (pp_access (pp_access pp_var_decl))
              (pp_indirect (pp_access pp_var_decl)))
           ((mem, ("_reg", m)),
            (self, ("_reg", m)))
       | MStep ([i0], i, vl)
         when Basic_library.is_value_internal_fun
             (mk_val (Fun (i, vl)) i0.var_type)  ->
         prev_ghost fmt ()
       | MStep (_, i, _) when !Options.mpfr && Mpfr.is_homomorphic_fun i ->
         prev_ghost fmt ()
       | MStep ([_], i, _) when has_c_prototype i dependencies ->
         prev_ghost fmt ()
       | MStep (_, i, _)
       | MReset i ->
         begin try
             let n, _ = List.assoc i m.minstances in
             pred
               (pp_mem_ghost pp_access' pp_indirect')
               (node_name n, (mem, i), (self, i))
           with Not_found -> prev_ghost fmt ()
         end
       | _ -> prev_ghost fmt ())
    ~i:(i+1) fmt instr.instr_desc

let print_machine_ghost_struct fmt m =
  pp_spec (pp_ghost (print_machine_struct ~ghost:true)) fmt m

let print_machine_ghost_simulations dependencies fmt m =
  if not (fst (Machine_code_common.get_stateless_status m)) then
    let name = m.mname.node_id in
    let self = mk_self m in
    let mem = mk_mem m in
    fprintf fmt "%a@,%a@,%a%a"
      print_machine_ghost_struct m
      (print_machine_ghost_simulation_aux m pp_true ~i:0) ()
      (pp_print_list_i
        ~pp_epilogue:pp_print_cut
        ~pp_open_box:pp_open_vbox0
        (print_machine_ghost_simulation dependencies m))
      m.mstep.step_instrs
      (print_machine_ghost_simulation_aux m
         (pp_mem_ghost' ~i:(List.length m.mstep.step_instrs))) (name, mem, self)

let print_machine_core_annotations dependencies fmt m =
  if not (fst (Machine_code_common.get_stateless_status m)) then
    let name = m.mname.node_id in
    let self = mk_self m in
    let mem = mk_mem m in
    fprintf fmt "%a@,%a@,%a%a"
      print_machine_ghost_struct m
      (print_machine_ghost_simulation_aux m pp_true ~i:0) ()
      (pp_print_list_i
        ~pp_epilogue:pp_print_cut
        ~pp_open_box:pp_open_vbox0
        (print_machine_ghost_simulation dependencies m))
      m.mstep.step_instrs
      (print_machine_ghost_simulation_aux m
         (pp_mem_ghost' ~i:(List.length m.mstep.step_instrs))) (name, mem, self)

let pp_at pp_p fmt (p, l) =
  fprintf fmt "\\at(%a, %s)" pp_p p l

let label_pre = "Pre"

let pp_at_pre pp_p fmt p =
  pp_at pp_p fmt (p, label_pre)

module VarDecl = struct
  type t = var_decl
  let compare v1 v2 = compare v1.var_id v2.var_id
end
module VDSet = Set.Make(VarDecl)

let pp_arrow_spec fmt () =
  let name = "_arrow" in
  let mem_in = "mem_in" in
  let mem_out = "mem_out" in
  let reg_first = "_reg", "_first" in
  let mem_in_first = mem_in, reg_first in
  let mem_out_first = mem_out, reg_first in
  let mem = "mem" in
  let self = "self" in
  fprintf fmt "/* ACSL arrow spec */@,%a%a%a%a"
    (pp_spec_line (pp_ghost pp_print_string))
    "struct _arrow_mem_ghost {struct _arrow_reg _reg;};"
    (pp_spec_cut
       (pp_predicate
          (pp_mem_init pp_machine_decl)
          (pp_equal
             (pp_access pp_access')
             pp_print_string)))
    ((name, (name, "mem_ghost", mem_in)),
     (mem_in_first, "true"))
    (pp_spec_cut
       (pp_predicate
          (pp_mem_trans_aux
             pp_machine_decl pp_machine_decl pp_print_string pp_print_string)
          (pp_and
             (pp_equal
                pp_print_string
                (pp_access pp_access'))
             (pp_ite
                (pp_access pp_access')
                (pp_equal
                   (pp_access pp_access')
                   pp_print_string)
                (pp_equal
                   (pp_access pp_access')
                   (pp_access pp_access'))))))
    ((name, [], ["_Bool out"], (name, "mem_ghost", mem_in), (name, "mem_ghost", mem_out)),
     (("out", mem_in_first),
      (mem_in_first, (mem_out_first, "false"), (mem_out_first, mem_in_first))))
    (pp_spec_cut
       (pp_predicate
          (pp_mem_ghost pp_machine_decl pp_machine_decl)
          (pp_equal
             (pp_access pp_access')
             (pp_indirect pp_access'))))
    ((name, (name, "mem_ghost", mem), (name, "mem", "*" ^ self)),
    ((mem, reg_first), (self, reg_first)))

module SrcMod = struct

  let pp_predicates dependencies fmt machines =
    fprintf fmt
      "%a@,%a%a%a"
      pp_arrow_spec ()
      (pp_print_list
         ~pp_open_box:pp_open_vbox0
         ~pp_prologue:(pp_print_endcut "/* ACSL `valid` predicates */")
         print_machine_valid_predicate
         ~pp_epilogue:pp_print_cutcut) machines
      (pp_print_list
         ~pp_open_box:pp_open_vbox0
         ~pp_sep:pp_print_cutcut
         ~pp_prologue:(pp_print_endcut "/* ACSL ghost simulations */")
         (print_machine_ghost_simulations dependencies)
         ~pp_epilogue:pp_print_cutcut) machines
      (pp_print_list
         ~pp_open_box:pp_open_vbox0
         ~pp_sep:pp_print_cutcut
         ~pp_prologue:(pp_print_endcut "/* ACSL core annotations */")
         (print_machine_core_annotations dependencies)
         ~pp_epilogue:pp_print_cutcut) machines

  let pp_reset_spec fmt self m =
    let name = m.mname.node_id in
    let mem = mk_mem m in
    pp_spec_cut (fun fmt () ->
        fprintf fmt
          "%a@,%a@,%a@,%a"
          (pp_requires pp_mem_valid') (name, self)
          (pp_requires (pp_separated self)) m.minstances
          (pp_assigns
             (pp_print_list
                ~pp_sep:pp_print_comma
                ~pp_nil:pp_nothing
                (pp_inst self))) m.minstances
          (pp_ensures
             (pp_forall
                pp_machine_decl
                (pp_implies
                   pp_mem_ghost'
                   pp_mem_init')))
          ((name, "mem_ghost", mem),
           ((name, mem, self), (name, mem))))
      fmt ()

  let pp_step_spec fmt self m =
    let name = m.mname.node_id in
    let mem_in = mk_mem_in m in
    let mem_out = mk_mem_out m in
    pp_spec_cut (fun fmt () ->
        fprintf fmt
          "%a@,%a@,%a@,%a@,%a"
          (pp_requires (pp_valid pp_var_decl)) m.mstep.step_outputs
          (pp_requires pp_mem_valid') (name, self)
          (pp_requires (pp_separated self)) m.minstances
          (pp_assigns
             (if m.mstep.step_outputs = [] && m.minstances = [] then
                pp_nothing
              else
                fun fmt () ->
                  fprintf fmt "@[<h>%a%a@]"
                    (pp_print_list
                       ~pp_sep:pp_print_comma
                       ~pp_epilogue:pp_print_comma
                       pp_ptr_decl) m.mstep.step_outputs
                    (pp_print_list
                       ~pp_sep:pp_print_comma
                       (pp_inst self)) m.minstances)) ()
          (pp_ensures
             (pp_forall
                (fun fmt () ->
                   fprintf fmt "%a, %s"
                     pp_machine_decl (name, "mem_ghost", mem_in)
                     mem_out)
                (pp_implies
                   (pp_at_pre pp_mem_ghost')
                   (pp_implies
                      pp_mem_ghost'
                      pp_mem_trans'))))
          ((),
           ((name, mem_in, self),
            ((name, mem_out, self),
             (m, mem_in, mem_out)))))
      fmt ()

  let pp_step_instr_spec m self fmt (i, _instr) =
    let name = m.mname.node_id in
    let mem_in = mk_mem_in m in
    let mem_out = mk_mem_out m in
    fprintf fmt "@,%a"
      (pp_spec
         (pp_assert
            (pp_forall
               (fun fmt () ->
                  fprintf fmt "%a, %s"
                    pp_machine_decl (name, "mem_ghost", mem_in)
                    mem_out)
               (pp_implies
                  (pp_at_pre pp_mem_ghost')
                  (pp_implies
                     (pp_mem_ghost' ~i:(i+1))
                     (pp_mem_trans' ~i:(i+1)))))))
      ((),
       ((name, mem_in, self),
        ((name, mem_out, self),
         (m, mem_in, mem_out))))

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
