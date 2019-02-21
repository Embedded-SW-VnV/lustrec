(********************************************************************)
(*                                                                  *)
(*  The LustreC compiler toolset   /  The LustreC Development Team  *)
(*  Copyright 2012 -    --   ONERA - CNRS - INPT - ISAE-SUPAERO     *)
(*                                                                  *)
(*  LustreC is free software, distributed WITHOUT ANY WARRANTY      *)
(*  under the terms of the GNU Lesser General Public License        *)
(*  version 2.1.                                                    *)
(*                                                                  *)
(********************************************************************)

open Format

open Machine_code_types
open Lustre_types
open Corelang
open Machine_code_common
open Ada_backend_common

(** Main module for generating packages bodies
 **)
module Main =
struct

  (* Printing functions for basic operations and expressions *)
  (* TODO: refactor code -> use let rec and for basic pretty printing
     function *)
  (** Printing function for Ada tags, mainly booleans.

      @param fmt the formater to use
      @param t the tag to print
   **)
  let pp_ada_tag fmt t =
    pp_print_string fmt
      (if t = tag_true then "True" else if t = tag_false then "Flase" else t)

  (** Printing function for machine type constants. For the moment,
      arrays are not supported.

      @param fmt the formater to use
      @param c the constant to print
   **)
  let pp_ada_const fmt c =
    match c with
    | Const_int i                     -> pp_print_int fmt i
    | Const_real (c, e, s)            -> pp_print_string fmt s
    | Const_tag t                     -> pp_ada_tag fmt t
    | Const_string _ | Const_modeid _ ->
      (Format.eprintf
         "internal error: Ada_backend_adb.pp_ada_const cannot print string or modeid.";
       assert false)
    | _                               ->
      raise (Ada_not_supported "unsupported: Ada_backend_adb.pp_ada_const does not
      support this constant")

  (** Printing function for expressions [v1 modulo v2]. Depends
      on option [integer_div_euclidean] to choose between mathematical
      modulo or remainder ([rem] in Ada).

      @param pp_value pretty printer for values
      @param v1 the first value in the expression
      @param v2 the second value in the expression
      @param fmt the formater to print on
   **)
  let pp_mod pp_value v1 v2 fmt =
    if !Options.integer_div_euclidean then
      (* (a rem b) + (a rem b < 0 ? abs(b) : 0) *)
      Format.fprintf fmt
        "((%a rem %a) + (if (%a rem %a) < 0 then abs(%a) else 0))"
        pp_value v1 pp_value v2
        pp_value v1 pp_value v2
        pp_value v2
    else (* Ada behavior for rem *)
      Format.fprintf fmt "(%a rem %a)" pp_value v1 pp_value v2

  (** Printing function for expressions [v1 div v2]. Depends on
      option [integer_div_euclidean] to choose between mathematic
      division or Ada division.

      @param pp_value pretty printer for values
      @param v1 the first value in the expression
      @param v2 the second value in the expression
      @param fmt the formater to print in
   **)
  let pp_div pp_value v1 v2 fmt =
    if !Options.integer_div_euclidean then
      (* (a - ((a rem b) + (if a rem b < 0 then abs (b) else 0))) / b) *)
      Format.fprintf fmt "(%a - %t) / %a"
        pp_value v1
        (pp_mod pp_value v1 v2)
        pp_value v2
    else (* Ada behavior for / *)
      Format.fprintf fmt "(%a / %a)" pp_value v1 pp_value v2

  (** Printing function for basic lib functions.

      @param pp_value pretty printer for values
      @param i a string representing the function
      @param fmt the formater to print on
      @param vl the list of operands
   **)
  let pp_basic_lib_fun pp_value ident fmt vl =
    match ident, vl with
    | "uminus", [v]    ->
      Format.fprintf fmt "(- %a)" pp_value v
    | "not", [v]       ->
      Format.fprintf fmt "(not %a)" pp_value v
    | "impl", [v1; v2] ->
      Format.fprintf fmt "(not %a or else %a)" pp_value v1 pp_value v2
    | "=", [v1; v2]    ->
      Format.fprintf fmt "(%a = %a)" pp_value v1 pp_value v2
    | "mod", [v1; v2]  -> pp_mod pp_value v1 v2 fmt
    | "equi", [v1; v2] ->
      Format.fprintf fmt "((not %a) = (not %a))" pp_value v1 pp_value v2
    | "xor", [v1; v2]  ->
      Format.fprintf fmt "((not %a) \\= (not %a))" pp_value v1 pp_value v2
    | "/", [v1; v2]    -> pp_div pp_value v1 v2 fmt
    | op, [v1; v2]     ->
      Format.fprintf fmt "(%a %s %a)" pp_value v1 op pp_value v2
    | fun_name, _      ->
      (Format.eprintf "internal compilation error: basic function %s@." fun_name; assert false)

  (** Printing function for values.

      @param fmt the formater to use
      @param value the value to print. Should be a
             {!type:Machine_code_types.value_t} value
   **)
  let rec pp_value fmt value =
    match value.value_desc with
    | Cst c             -> pp_ada_const fmt c
    | Var var_name      -> pp_var_name fmt var_name
    | Fun (f_ident, vl) -> pp_basic_lib_fun pp_value f_ident fmt vl
    | _                 ->
      raise (Ada_not_supported
               "unsupported: Ada_backend.adb.pp_value does not support this value type")

  (** Printing function for basic assignement [var_name := value;].

      @param fmt the formater to print on
      @param var_name the name of the variable
      @param value the value to be assigned
   **)
  let pp_basic_assign fmt var_name value =
    fprintf fmt "%a := %a"
      pp_var_name var_name
      pp_value value

  (** Printing function for assignement. For the moment, only use
      [pp_basic_assign] function.

      @param pp_var pretty printer for variables
      @param fmt the formater to print on
      @param var_name the name of the variable
      @param value the value to be assigned
   **)
  let pp_assign pp_var fmt var_name value = pp_basic_assign

  (* Printing function for reset function *)
  (* TODO: clean the call to extract_node *)
  (** Printing function for reset function name.

      @param fmt the formater to use
      @param encapsulated_node the node encapsulated in a pair
             [(instance, (node, static))]
   **)
  let pp_machine_reset_name fmt encapsulated_node =
    fprintf fmt "%a.reset" pp_package_name (extract_node encapsulated_node)

  (** Printing function for reset function.

      @param machine the considered machine
      @param fmt the formater to use
      @param instance the considered instance
   **)
  let pp_machine_reset (machine: machine_t) fmt instance =
    let (node, static) =
      try
        List.assoc instance machine.minstances
      with Not_found -> (Format.eprintf "internal error: pp_machine_reset %s %s:@." machine.mname.node_id instance; raise Not_found) in
    fprintf fmt "%a(state.%s)"
      pp_machine_reset_name (instance, (node, static))
      instance

  (** Printing function for instruction. See
      {!type:Machine_code_types.instr_t} for more details on
      machine types.

      @param machine the current machine
      @param fmt the formater to print on
      @param instr the instruction to print
   **)
  let pp_machine_instr machine fmt instr =
    match get_instr_desc instr with
    (* no reset *)
    | MNoReset _ -> ()
    (* reset  *)
    | MReset ident ->
      pp_machine_reset machine fmt ident
    | MLocalAssign (ident, value) ->
      pp_basic_assign fmt ident value
    | MStateAssign (i,v) ->
      fprintf fmt "MStateAssign"
    (* pp_assign
       *   m self (pp_c_var_read m) fmt
       *   i.var_type (mk_val (Var i) i.var_type) v *)
    | MStep ([i0], i, vl) when Basic_library.is_value_internal_fun
          (mk_val (Fun (i, vl)) i0.var_type)  ->
      fprintf fmt "MStep basic"
    (* pp_machine_instr dependencies m self fmt
     *   (update_instr_desc instr (MLocalAssign (i0, mk_val (Fun (i, vl)) i0.var_type))) *)
    | MStep (il, i, vl) -> fprintf fmt "MStep"

    (* pp_basic_instance_call m self fmt i vl il *)
    | MBranch (_, []) -> fprintf fmt "MBranch []"

    (* (Format.eprintf "internal error: C_backend_src.pp_machine_instr %a@." (pp_instr m) instr; assert false) *)
    | MBranch (g, hl) -> fprintf fmt "MBranch gen"
    (* if let t = fst (List.hd hl) in t = tag_true || t = tag_false
     * then (\* boolean case, needs special treatment in C because truth value is not unique *\)
     *   (\* may disappear if we optimize code by replacing last branch test with default *\)
     *   let tl = try List.assoc tag_true  hl with Not_found -> [] in
     *   let el = try List.assoc tag_false hl with Not_found -> [] in
     *   pp_conditional dependencies m self fmt g tl el
     * else (\* enum type case *\)
     *   (\*let g_typ = Typing.type_const Location.dummy_loc (Const_tag (fst (List.hd hl))) in*\)
     *   fprintf fmt "@[<v 2>switch(%a) {@,%a@,}@]"
     *     (pp_c_val m self (pp_c_var_read m)) g
     *     (Utils.fprintf_list ~sep:"@," (pp_machine_branch dependencies m self)) hl *)
    | MComment s  ->
      fprintf fmt "-- %s@ " s
    | _ -> fprintf fmt "Don't  know"


(** Keep only the MReset from an instruction list.
  @param list to filter
**)
let filter_reset instr_list = List.map
    (fun i -> match get_instr_desc i with MReset i -> i | _ -> assert false)
  instr_list

(** Print the definition of the init procedure from a machine.
   @param fmt the formater to print on
   @param machine the machine
**)
let pp_init_definition fmt m = pp_procedure_definition
      pp_init_procedure_name
      (pp_init_prototype m)
      (pp_machine_var_decl NoMode)
      (pp_machine_instr m)
      fmt
      ([], m.minit)

(** Print the definition of the step procedure from a machine.
   @param fmt the formater to print on
   @param machine the machine
**)
let pp_step_definition fmt m = pp_procedure_definition
      pp_step_procedure_name
      (pp_step_prototype m)
      (pp_machine_var_decl NoMode)
      (pp_machine_instr m)
      fmt
      (m.mstep.step_locals, m.mstep.step_instrs)

(** Print the definition of the reset procedure from a machine.
   @param fmt the formater to print on
   @param machine the machine
**)
let pp_reset_definition fmt m = pp_procedure_definition
      pp_reset_procedure_name
      (pp_reset_prototype m)
      (pp_machine_var_decl NoMode)
      (pp_machine_instr m)
      fmt
      ([], m.minit)

(** Print the definition of the clear procedure from a machine.
   @param fmt the formater to print on
   @param machine the machine
**)
let pp_clear_definition fmt m = pp_procedure_definition
      pp_clear_procedure_name
      (pp_clear_prototype m)
      (pp_machine_var_decl NoMode)
      (pp_machine_instr m)
      fmt
      ([], m.minit)

(** Print the package definition(adb) of a machine.
   @param fmt the formater to print on
   @param machine the machine
**)
let pp_file fmt machine =
  fprintf fmt "%a@,  @[<v>@,%a;@,@,%a;@,@,%a;@,@,%a;@,@]@,%a;@."
    (pp_begin_package true) machine (*Begin the package*)
    pp_init_definition machine (*Define the init procedure*)
    pp_step_definition machine (*Define the step procedure*)
    pp_reset_definition machine (*Define the reset procedure*)
    pp_clear_definition machine (*Define the clear procedure*)
    pp_end_package machine  (*End the package*)

end

(* Local Variables: *)
(* compile-command: "make -C ../../.." *)
(* End: *)
