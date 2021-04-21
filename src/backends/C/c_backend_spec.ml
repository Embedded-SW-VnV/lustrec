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
(* let pp_acsl_preamble fmt _preamble =
 *   fprintf fmt "";
 *   () *)

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

module VarDecl = struct
  type t = var_decl
  let compare v1 v2 = compare v1.var_id v2.var_id
end
module VDSet = Set.Make(VarDecl)

module Live = Map.Make(Int)

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

let pp_assigns pp =
  pp_print_list
    ~pp_prologue:(fun fmt () -> pp_print_string fmt "assigns ")
    ~pp_epilogue:pp_print_semicolon'
    ~pp_sep:pp_print_comma
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

(* let memories machines m =
 *   let open List in
 *   let grow paths i =
 *     match paths with
 *     | [] -> [[i]]
 *     | _ -> map (cons i) paths
 *   in
 *   let rec aux paths m =
 *     map (fun (i, (td, _)) ->
 *         let paths = grow paths i in
 *         try
 *           let m = find (fun m -> m.mname.node_id = node_name td) machines in
 *           aux paths m
 *         with Not_found -> paths)
 *       m.minstances |> flatten
 *   in
 *   aux [] m |> map rev *)

let instances machines m =
  let open List in
  let grow paths i mems =
    match paths with
    | [] -> [[i, mems]]
    | _ -> map (cons (i, mems)) paths
  in
  let rec aux paths m =
    map (fun (i, (td, _)) ->
        try
          let m = find (fun m -> m.mname.node_id = node_name td) machines in
          aux (grow paths i m.mmemory) m
        with Not_found -> grow paths i [])
      m.minstances |> flatten
  in
  aux [] m |> map rev

let memories insts =
  List.(map (fun path ->
      let mems = snd (hd (rev path)) in
      map (fun mem -> path, mem) mems) insts |> flatten)

let pp_instance =
  pp_print_list
    ~pp_prologue:(fun fmt () -> pp_print_string fmt "self->")
    ~pp_sep:(fun fmt () -> pp_print_string fmt "->")
    (fun fmt (i, _) -> pp_print_string fmt i)

let pp_memory fmt (path, mem) =
  pp_access (pp_indirect pp_instance pp_print_string) pp_var_decl
    fmt ((path, "_reg"), mem)
  (* let mems = snd List.(hd (rev path)) in
   * pp_print_list
   *   ~pp_sep:pp_print_comma
   *   (fun fmt mem -> pp_access pp_instance pp_var_decl fmt (path, mem))
   *   fmt
   *   mems *)
  (* let mems = ref [] in
   * let pp fmt =
   *   pp_print_list
   *     ~pp_prologue:(fun fmt () -> pp_print_string fmt "self->")
   *     ~pp_sep:(fun fmt () -> pp_print_string fmt "->")
   *     (fun fmt (i, regs) -> mems := regs; pp_print_string fmt i)
   *     fmt
   * in
   * pp_print_list
   *   ~pp_sep:pp_print_comma
   *   (fun fmt mem -> pp_access pp pp_var_decl fmt (insts, mem))
   *   fmt !mems *)

let prefixes l =
  let rec pref acc = function
    | x :: l -> pref ([x] :: List.map (List.cons x) acc) l
    | [] -> acc
  in
  pref [] (List.rev l)

let powerset_instances paths =
  List.map prefixes paths |> List.flatten

let pp_separated self fmt (paths, ptrs) =
  fprintf fmt "\\separated(@[<h>%s%a%a@])"
    self
    (pp_print_list
       ~pp_prologue:pp_print_comma
       ~pp_sep:pp_print_comma
       pp_instance)
    paths
    (pp_print_list
       ~pp_prologue:pp_print_comma
       ~pp_sep:pp_print_comma
       pp_var_decl)
    ptrs

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

let pp_valid pp =
  pp_and_l
  (* pp_print_list *)
    (* ~pp_sep:pp_print_cut *)
    (fun fmt x -> fprintf fmt "\\valid(%a)" pp x)

let pp_ite pp_c pp_t pp_f fmt (c, t, f) =
  fprintf fmt "(%a @[<hov>? %a@ : %a)@]"
    pp_c c
    pp_t t
    pp_f f

let pp_paren pp fmt v =
  fprintf fmt "(%a)" pp v

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
  fprintf fmt "%s_initialization(%a)" name pp_mem mem

let pp_mem_init' = pp_mem_init pp_print_string

let pp_locals m fmt vs =
  pp_print_list
    ~pp_open_box:pp_open_hbox
    ~pp_sep:pp_print_comma
    (pp_c_decl_local_var ~pp_c_basic_type_desc:pp_acsl_basic_type_desc m) fmt vs

let pp_ptr_decl fmt v =
  fprintf fmt "*%s" v.var_id

let pp_basic_assign_spec pp_l pp_r fmt typ var_name value =
  if Types.is_real_type typ && !Options.mpfr
  then
    assert false
    (* Mpfr.pp_inject_assign pp_var fmt (var_name, value) *)
  else
    pp_equal pp_l pp_r fmt (var_name, value)

let pp_assign_spec
    m self_l pp_var_l self_r pp_var_r fmt (var_type, var_name, value) =
  let depth = expansion_depth value in
  let loop_vars = mk_loop_variables m var_type depth in
  let reordered_loop_vars = reorder_loop_variables loop_vars in
  let rec aux typ fmt vars =
    match vars with
    | [] ->
      pp_basic_assign_spec
        (pp_value_suffix ~indirect:false m self_l var_type loop_vars pp_var_l)
        (pp_value_suffix ~indirect:false m self_r var_type loop_vars pp_var_r)
        fmt typ var_name value
    | (d, LVar i) :: q ->
      assert false
      (* let typ' = Types.array_element_type typ in
       * fprintf fmt "@[<v 2>{@,int %s;@,for(%s=0;%s<%a;%s++)@,%a @]@,}"
       *   i i i pp_c_dimension d i
       *   (aux typ') q *)
    | (d, LInt r) :: q ->
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
    if Machine_code_common.is_memory m id
    && not (Types.is_real_type id.var_type && !Options.mpfr)
    then fprintf fmt "(*%s)" id.var_id
    else fprintf fmt "%s" id.var_id
  else
    fprintf fmt "%s" id.var_id

let rec assigned s instr =
  let open VDSet in
  match instr.instr_desc with
  | MLocalAssign (x, _) ->
    add x s
  | MStep (xs, _, _) ->
    union s (of_list xs)
  | MBranch (_, brs) ->
    List.(fold_left (fun s (_, instrs) -> fold_left assigned s instrs) s brs)
  | _ -> s

let rec occur_val s v =
  let open VDSet in
  match v.value_desc with
  | Var x ->
    add x s
  | Fun (_, vs)
  | Array vs ->
    List.fold_left occur_val s vs
  | Access (v1, v2)
  | Power (v1, v2) ->
    occur_val (occur_val s v1) v2
  | _ -> s

let rec occur s instr =
  let open VDSet in
  match instr.instr_desc with
  | MLocalAssign (_, v)
  | MStateAssign (_, v) ->
    occur_val s v
  | MStep (_, _, vs) ->
    List.fold_left occur_val s vs
  | MBranch (v, brs) ->
    List.(fold_left (fun s (_, instrs) -> fold_left occur s instrs)
            (occur_val s v) brs)
  | _ -> s

let live = Hashtbl.create 32

let set_live_of m =
  let open VDSet in
  let locals = of_list m.mstep.step_locals in
  let outputs = of_list m.mstep.step_outputs in
  let vars = union locals outputs in
  let no_occur_after i =
    let occ, _ = List.fold_left (fun (s, j) instr ->
        if j <= i then (s, j+1) else (occur s instr, j+1))
        (empty, 0) m.mstep.step_instrs in
    diff locals occ
  in
  let l, _, _ = List.fold_left (fun (l, asg, i) instr ->
      let asg = inter (assigned asg instr) vars in
      Live.add (i + 1) (diff asg (no_occur_after i)) l, asg, i + 1)
      (Live.empty, empty, 0) m.mstep.step_instrs in
  Hashtbl.add live m.mname.node_id (Live.add 0 empty l)

let live_i m i =
  Live.find i (Hashtbl.find live m.mname.node_id)

let pp_mem_trans_aux ?i pp_mem_in pp_mem_out pp_input pp_output fmt
    (name, inputs, locals, outputs, mem_in, mem_out) =
  fprintf fmt "%s_transition%a(@[<hov>%a,@ %a%a%a%a@])"
    name
    (pp_print_option pp_print_int) i
    pp_mem_in mem_in
    (pp_print_list
       ~pp_epilogue:pp_print_comma
       ~pp_sep:pp_print_comma
       pp_input) inputs
    (pp_print_option
       (fun fmt _ ->
          pp_print_list
            ~pp_epilogue:pp_print_comma
            ~pp_sep:pp_print_comma
            pp_input fmt locals))
    i
    pp_mem_out mem_out
    (pp_print_list
       ~pp_prologue:pp_print_comma
       ~pp_sep:pp_print_comma
       pp_output) outputs

let pp_mem_trans ?i pp_mem_in pp_mem_out pp_input pp_output fmt
    (m, mem_in, mem_out) =
  let locals, outputs = match i with
    | Some 0 ->
      [], []
    | Some i when i < List.length m.mstep.step_instrs ->
      let li = live_i m i in
      VDSet.(inter (of_list m.mstep.step_locals) li |> elements,
             inter (of_list m.mstep.step_outputs) li |> elements)
    | Some _ ->
      [], m.mstep.step_outputs
    | _ ->
      m.mstep.step_locals, m.mstep.step_outputs
  in
  pp_mem_trans_aux ?i pp_mem_in pp_mem_out pp_input pp_output fmt
    (m.mname.node_id,
     m.mstep.step_inputs,
     locals,
     outputs,
     mem_in,
     mem_out)

let pp_mem_trans' ?i fmt =
  pp_mem_trans ?i pp_print_string pp_print_string pp_var_decl pp_var_decl fmt
let pp_mem_trans'' ?i fmt =
  pp_mem_trans ?i pp_print_string pp_print_string pp_var_decl pp_ptr_decl fmt

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

let print_ghost_simulation dependencies m fmt (i, instr) =
  let name = m.mname.node_id in
  let self = mk_self m in
  let mem = mk_mem m in
  let prev_ghost fmt () = pp_mem_ghost' ~i fmt (name, mem, self) in
  let pred pp v = pp_and prev_ghost pp fmt ((), v) in
  let rec aux fmt instr =
    match instr.instr_desc with
    | MStateAssign (m, _) ->
      pp_equal
        (pp_access pp_print_string (pp_access pp_print_string pp_var_decl))
        (pp_indirect pp_print_string (pp_access pp_print_string pp_var_decl))
        fmt
        ((mem, ("_reg", m)), (self, ("_reg", m)))
    | MStep ([i0], i, vl)
      when Basic_library.is_value_internal_fun
          (mk_val (Fun (i, vl)) i0.var_type)  ->
      pp_true fmt ()
    | MStep (_, i, _) when !Options.mpfr && Mpfr.is_homomorphic_fun i ->
      pp_true fmt ()
    | MStep ([_], i, _) when has_c_prototype i dependencies ->
      pp_true fmt ()
    | MStep (_, i, _)
    | MReset i ->
      begin try
          let n, _ = List.assoc i m.minstances in
          pp_mem_ghost pp_access' pp_indirect' fmt
            (node_name n, (mem, i), (self, i))
        with Not_found -> pp_true fmt ()
      end
    | MBranch (_, brs) ->
      (* TODO: handle branches *)
      pp_and_l aux fmt List.(flatten (map snd brs))
    | _ -> pp_true fmt ()
  in
  pred aux instr

let print_machine_ghost_simulation dependencies m fmt i instr =
  print_machine_ghost_simulation_aux m
    (print_ghost_simulation dependencies m)
    ~i:(i+1)
    fmt (i, instr)

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

let print_machine_trans_simulation_aux ?i m pp fmt v =
  let name = m.mname.node_id in
  let mem_in = mk_mem_in m in
  let mem_out = mk_mem_out m in
  pp_spec
    (pp_predicate
       (pp_mem_trans pp_machine_decl pp_machine_decl
          (pp_c_decl_local_var ~pp_c_basic_type_desc:pp_acsl_basic_type_desc m)
          (pp_c_decl_local_var ~pp_c_basic_type_desc:pp_acsl_basic_type_desc m)
          ?i)
       pp)
    fmt
    ((m, (name, "mem_ghost", mem_in), (name, "mem_ghost", mem_out)),
     v)

let print_trans_simulation machines dependencies m fmt (i, instr) =
  let mem_in = mk_mem_in m in
  let mem_out = mk_mem_out m in
  let d = VDSet.(diff (union (live_i m i) (assigned empty instr))
                   (live_i m (i+1))) in
  (* XXX *)
  (* printf "%d : %a\n%d : %a\nocc: %a\n\n"
   *   i
   *   (pp_print_parenthesized pp_var_decl) (VDSet.elements (live_i m i))
   *   (i+1)
   *   (pp_print_parenthesized pp_var_decl) (VDSet.elements (live_i m (i+1)))
   *   (pp_print_parenthesized pp_var_decl) VDSet.(elements (assigned empty instr)); *)
  let prev_trans fmt () = pp_mem_trans' ~i fmt (m, mem_in, mem_out) in
  let pred pp v =
    let vars = VDSet.(union (of_list m.mstep.step_locals)
                        (of_list m.mstep.step_outputs)) in
    let locals = VDSet.(inter vars d |> elements) in
    if locals = []
    then pp_and prev_trans pp fmt ((), v)
    else pp_exists (pp_locals m) (pp_and prev_trans pp) fmt (locals, ((), v))
  in
  let rec aux fmt instr = match instr.instr_desc with
    | MLocalAssign (x, v)
    | MStateAssign (x, v) ->
      pp_assign_spec m mem_out (pp_c_var_read m) mem_in (pp_c_var_read m) fmt
        (x.var_type, mk_val (Var x) x.var_type, v)
    | MStep ([i0], i, vl)
      when Basic_library.is_value_internal_fun
          (mk_val (Fun (i, vl)) i0.var_type)  ->
      pp_true fmt ()
    | MStep (_, i, _) when !Options.mpfr && Mpfr.is_homomorphic_fun i ->
      pp_true fmt ()
    | MStep ([_], i, _) when has_c_prototype i dependencies ->
      pp_true fmt ()
    | MStep (xs, i, ys) ->
      begin try
          let n, _ = List.assoc i m.minstances in
            pp_mem_trans_aux
              pp_access' pp_access'
              (pp_c_val m mem_in (pp_c_var_read m))
              pp_var_decl
              fmt
              (node_name n, ys, [], xs, (mem_in, i), (mem_out, i))
        with Not_found -> pp_true fmt ()
      end
    | MReset i ->
      begin try
          let n, _ = List.assoc i m.minstances in
          pp_mem_init' fmt (node_name n, mem_out)
        with Not_found -> pp_true fmt ()
      end
    | MBranch (v, brs) ->
      if let t = fst (List.hd brs) in t = tag_true || t = tag_false
      then (* boolean case *)
        pp_ite (pp_c_val m mem_in (pp_c_var_read m))
          (fun fmt () ->
             match List.assoc tag_true brs with
             | _ :: _ as l -> pp_paren (pp_and_l aux) fmt l
             | []
             | exception Not_found -> pp_true fmt ())
          (fun fmt () ->
             match List.assoc tag_false brs with
             | _ :: _ as l -> pp_paren (pp_and_l aux) fmt l
             | []
             | exception Not_found ->
             (* try
              *   let l = List.assoc tag_false brs in
              *   pp_paren (pp_and_l aux) fmt l
              * with Not_found -> *) pp_true fmt ())
          
          (* (pp_paren (pp_and_l aux)) (pp_paren (pp_and_l aux)) *)
          fmt (v, (), ())
      else (* enum type case *)
      pp_and_l (fun fmt (l, instrs) ->
          let pp_val = pp_c_val m mem_in (pp_c_var_read m) in
          (* if l = tag_false then
           *   pp_paren (pp_implies
           *               (pp_different pp_val pp_c_tag)
           *               (pp_and_l aux))
           *     fmt
           *     ((v, tag_true), instrs)
           * else *)
            pp_paren (pp_implies
                        (pp_equal pp_val pp_c_tag)
                        (pp_and_l aux))
              fmt
              ((v, l), instrs))
        fmt brs
    | _ -> pp_true fmt ()
  in
  pred aux instr

let print_machine_trans_simulation machines dependencies m fmt i instr =
  print_machine_trans_simulation_aux m
    (print_trans_simulation machines dependencies m)
    ~i:(i+1)
    fmt (i, instr)

let print_machine_trans_annotations machines dependencies fmt m =
  if not (fst (Machine_code_common.get_stateless_status m)) then begin
    set_live_of m;
    let i = List.length m.mstep.step_instrs in
    let mem_in = mk_mem_in m in
    let mem_out = mk_mem_out m in
    let last_trans fmt () =
      let locals = VDSet.(inter
                            (of_list m.mstep.step_locals)
                            (live_i m i)
                          |> elements) in
      if locals = []
      then pp_mem_trans' ~i fmt (m, mem_in, mem_out)
      else pp_exists (pp_locals m) (pp_mem_trans' ~i) fmt
          (locals, (m, mem_in, mem_out))
    in
    fprintf fmt "%a@,%a%a"
      (print_machine_trans_simulation_aux m pp_true ~i:0) ()
      (pp_print_list_i
        ~pp_epilogue:pp_print_cut
        ~pp_open_box:pp_open_vbox0
        (print_machine_trans_simulation machines dependencies m))
      m.mstep.step_instrs
      (print_machine_trans_simulation_aux m last_trans) ()
  end

let print_machine_init_predicate fmt m =
  if not (fst (Machine_code_common.get_stateless_status m)) then
    let name = m.mname.node_id in
    let mem_in = mk_mem_in m in
    pp_spec
      (pp_predicate
         (pp_mem_init pp_machine_decl)
         (pp_and_l (fun fmt (i, (td, _)) ->
              pp_mem_init pp_access' fmt (node_name td, (mem_in, i)))))
      fmt
      ((name, (name, "mem_ghost", mem_in)), m.minstances)

let pp_at pp_p fmt (p, l) =
  fprintf fmt "\\at(%a, %s)" pp_p p l

let label_pre = "Pre"

let pp_at_pre pp_p fmt p =
  pp_at pp_p fmt (p, label_pre)

let pp_register =
  pp_print_list
    ~pp_prologue:(fun fmt () -> pp_print_string fmt "self->")
    ~pp_epilogue:(fun fmt () -> pp_print_string fmt "->_reg._first")
    ~pp_sep:(fun fmt () -> pp_print_string fmt "->")
    (fun fmt (i, _) -> pp_print_string fmt i)

module HdrMod = struct

  let print_machine_decl_prefix = fun _ _ -> ()

  let pp_import_standard_spec fmt () =
    fprintf fmt "@,#include \"%s/arrow_spec.h%s\""
      (Arrow.arrow_top_decl ()).top_decl_owner
      (if !Options.cpp then "pp" else "")

end

module SrcMod = struct

  let pp_predicates dependencies fmt machines =
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
         (print_machine_ghost_simulations dependencies)
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
         (print_machine_trans_annotations machines dependencies)
         ~pp_epilogue:pp_print_cutcut) machines

  let pp_reset_spec fmt machines self m =
    let name = m.mname.node_id in
    let mem = mk_mem m in
    let insts = instances machines m in
    pp_spec_cut (fun fmt () ->
        fprintf fmt
          "%a@,%a@,%a@,%a"
          (pp_requires pp_mem_valid') (name, self)
          (pp_requires (pp_separated self)) (powerset_instances insts, [])
          (pp_assigns pp_register) insts
          (pp_ensures
             (pp_forall
                pp_machine_decl
                (pp_implies
                   pp_mem_ghost'
                   pp_mem_init')))
          ((name, "mem_ghost", mem),
           ((name, mem, self), (name, mem))))
      fmt ()

  let pp_step_spec fmt machines self m =
    let name = m.mname.node_id in
    let mem_in = mk_mem_in m in
    let mem_out = mk_mem_out m in
    let insts = instances machines m in
    let insts' = powerset_instances insts in
    pp_spec_cut (fun fmt () ->
        fprintf fmt
          "%a@,%a@,%a@,%a@,%a@,%a@,%a@,%a"
          (pp_requires (pp_valid pp_var_decl)) m.mstep.step_outputs
          (pp_requires pp_mem_valid') (name, self)
          (pp_requires (pp_separated self)) (insts', m.mstep.step_outputs)
          (pp_assigns pp_ptr_decl) m.mstep.step_outputs
          (pp_assigns (pp_reg self)) m.mmemory
          (pp_assigns pp_memory) (memories insts')
          (pp_assigns pp_register) insts
          (pp_ensures
             (pp_forall
                pp_machine_decl
                (pp_forall
                   pp_machine_decl
                   (pp_implies
                      (pp_at_pre pp_mem_ghost')
                      (pp_implies
                         pp_mem_ghost'
                         pp_mem_trans'')))))
          ((name, "mem_ghost", mem_in),
           ((name, "mem_ghost", mem_out),
            ((name, mem_in, self),
             ((name, mem_out, self),
              (m, mem_in, mem_out)))))
      )
      fmt ()

  let pp_step_instr_spec m self fmt (i, _instr) =
    let name = m.mname.node_id in
    let mem_in = mk_mem_in m in
    let mem_out = mk_mem_out m in
    fprintf fmt "@,%a"
      (pp_spec
         (pp_assert
            (pp_forall
               pp_machine_decl
               (pp_forall
                  pp_machine_decl
                  (pp_implies
                     (pp_at_pre pp_mem_ghost')
                     (pp_implies
                        (pp_mem_ghost' ~i)
                        (pp_mem_trans'' ~i)))))))
      ((name, "mem_ghost", mem_in),
       ((name, "mem_ghost", mem_out),
        ((name, mem_in, self),
         ((name, mem_out, self),
          (m, mem_in, mem_out)))))

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
