open Format

open Machine_code_types
open Lustre_types
open Corelang
open Machine_code_common

open Ada_printer
open Misc_printer
open Misc_lustre_function

(** Exception for unsupported features in Ada backend **)
exception Ada_not_supported of string

(** Print the name of the state variable.
   @param fmt the formater to print on
**)
let pp_state_name fmt = fprintf fmt "state"
(** Print the type of the state variable.
   @param fmt the formater to print on
**)
let pp_state_type fmt = fprintf fmt "TState"
(** Print the name of the reset procedure
   @param fmt the formater to print on
**)
let pp_reset_procedure_name fmt = fprintf fmt "reset"
(** Print the name of the step procedure
   @param fmt the formater to print on
**)
let pp_step_procedure_name fmt = fprintf fmt "step"
(** Print the name of the main procedure.
   @param fmt the formater to print on
**)
let pp_main_procedure_name fmt = fprintf fmt "ada_main"
(** Print the name of the arrow package.
   @param fmt the formater to print on
**)
let pp_arrow_package_name fmt = fprintf fmt "Arrow"
(** Print the type of a polymorphic type.
   @param fmt the formater to print on
   @param id the id of the polymorphic type
**)
let pp_polymorphic_type id fmt = fprintf fmt "T_%i" id









(*TODO Check all this function with unit test, improve this system and
   add support for : "cbrt", "erf", "log10", "pow", "atan2".
*)
let ada_supported_funs =
  [("sqrt",  ("Ada.Numerics.Elementary_Functions", "Sqrt"));
   ("log",   ("Ada.Numerics.Elementary_Functions", "Log"));
   ("exp",   ("Ada.Numerics.Elementary_Functions", "Exp"));
   ("pow",   ("Ada.Numerics.Elementary_Functions", "**"));
   ("sin",   ("Ada.Numerics.Elementary_Functions", "Sin"));
   ("cos",   ("Ada.Numerics.Elementary_Functions", "Cos"));
   ("tan",   ("Ada.Numerics.Elementary_Functions", "Tan"));
   ("asin",  ("Ada.Numerics.Elementary_Functions", "Arcsin"));
   ("acos",  ("Ada.Numerics.Elementary_Functions", "Arccos"));
   ("atan",  ("Ada.Numerics.Elementary_Functions", "Arctan"));
   ("sinh",  ("Ada.Numerics.Elementary_Functions", "Sinh"));
   ("cosh",  ("Ada.Numerics.Elementary_Functions", "Cosh"));
   ("tanh",  ("Ada.Numerics.Elementary_Functions", "Tanh"));
   ("asinh", ("Ada.Numerics.Elementary_Functions", "Arcsinh"));
   ("acosh", ("Ada.Numerics.Elementary_Functions", "Arccosh"));
   ("atanh", ("Ada.Numerics.Elementary_Functions", "Arctanh"));
   
   ("ceil",  ("", "Float'Ceiling"));
   ("floor", ("", "Float'Floor"));
   ("fmod",  ("", "Float'Remainder"));
   ("round", ("", "Float'Rounding"));
   ("trunc", ("", "Float'Truncation"));

   ("fabs", ("", "abs"));]

let is_builtin_fun ident =
  List.mem ident Basic_library.internal_funs ||
    List.mem_assoc ident ada_supported_funs

(** Print the name of a package associated to a machine.
   @param fmt the formater to print on
   @param machine the machine
**)
let pp_package_name machine fmt =
  if is_arrow machine then
      fprintf fmt "%t" pp_arrow_package_name
  else
      fprintf fmt "%a" pp_clean_ada_identifier machine.mname.node_id


(** Print the integer type name.
   @param fmt the formater to print on
**)
let pp_integer_type fmt = fprintf fmt "Integer"

(** Print the float type name.
   @param fmt the formater to print on
**)
let pp_float_type fmt = fprintf fmt "Float"

(** Print the boolean type name.
   @param fmt the formater to print on
**)
let pp_boolean_type fmt = fprintf fmt "Boolean"


(** Print a type.
   @param fmt the formater to print on
   @param type the type
**)
let pp_type fmt typ = 
  (match (Types.repr typ).Types.tdesc with
    | Types.Tbasic Types.Basic.Tint  -> pp_integer_type fmt
    | Types.Tbasic Types.Basic.Treal -> pp_float_type fmt
    | Types.Tbasic Types.Basic.Tbool -> pp_boolean_type fmt
    | Types.Tunivar                  -> pp_polymorphic_type typ.Types.tid fmt
    | Types.Tbasic _                 -> eprintf "Tbasic@."; assert false (*TODO*)
    | Types.Tconst _                 -> eprintf "Tconst@."; assert false (*TODO*)
    | Types.Tclock _                 -> eprintf "Tclock@."; assert false (*TODO*)
    | Types.Tarrow _                 -> eprintf "Tarrow@."; assert false (*TODO*)
    | Types.Ttuple l                 -> eprintf "Ttuple %a @." (Utils.fprintf_list ~sep:" " Types.print_ty) l; assert false (*TODO*)
    | Types.Tenum _                  -> eprintf "Tenum@.";  assert false (*TODO*)
    | Types.Tstruct _                -> eprintf "Tstruct@.";assert false (*TODO*)
    | Types.Tarray _                 -> eprintf "Tarray@."; assert false (*TODO*)
    | Types.Tstatic _                -> eprintf "Tstatic@.";assert false (*TODO*)
    | Types.Tlink _                  -> eprintf "Tlink@.";  assert false (*TODO*)
    | Types.Tvar                     -> eprintf "Tvar@.";   assert false (*TODO*)
    (*| _ -> eprintf "Type error : %a@." Types.print_ty typ; assert false *)
  )

(** Return a default ada constant for a given type.
   @param cst_typ the constant type
**)
let default_ada_cst cst_typ = match cst_typ with
  | Types.Basic.Tint  -> Const_int 0
  | Types.Basic.Treal -> Const_real (Num.num_of_int 0, 0, "0.0")
  | Types.Basic.Tbool -> Const_tag tag_false
  | _ -> assert false

(** Make a default value from a given type.
   @param typ the type
**)
let mk_default_value typ =
  match (Types.repr typ).Types.tdesc with
    | Types.Tbasic t  -> mk_val (Cst (default_ada_cst t)) typ
    | _                              -> assert false (*TODO*)

(** Print the type of a variable.
   @param fmt the formater to print on
   @param id the variable
**)
let pp_var_type fmt id = 
  pp_type fmt id.var_type

(** Print a package name with polymorphic types specified.
   @param substitution correspondance between polymorphic type id and their instantiation
   @param fmt the formater to print on
   @param machine the machine
**)
let pp_package_name_with_polymorphic substitution machine fmt =
  let polymorphic_types = find_all_polymorphic_type machine in
  assert(List.length polymorphic_types = List.length substitution);
  let substituion = List.sort_uniq (fun x y -> fst x - fst y) substitution in
  assert(List.for_all2 (fun poly1 (poly2, _) -> poly1 = poly2)
            polymorphic_types substituion);
  let instantiated_types = snd (List.split substitution) in
  fprintf fmt "%t%t%a"
    (pp_package_name machine)
    (Utils.pp_final_char_if_non_empty "_" instantiated_types)
    (Utils.fprintf_list ~sep:"_" pp_type) instantiated_types

(** Print the name of a variable.
   @param fmt the formater to print on
   @param id the variable
**)
let pp_var_name fmt id =
  fprintf fmt "%a" pp_clean_ada_identifier id.var_id

(** Print the complete name of variable.
   @param m the machine to check if it is memory
   @param fmt the formater to print on
   @param var the variable
**)
let pp_access_var m fmt var =
  if is_memory m var then
    fprintf fmt "%t.%a" pp_state_name pp_var_name var
  else
    pp_var_name fmt var


(* Expression print functions *)

(* Printing functions for basic operations and expressions *)
(* TODO: refactor code -> use let rec and for basic pretty printing
   function *)
(** Printing function for Ada tags, mainly booleans.

    @param fmt the formater to use
    @param t the tag to print
 **)
let pp_ada_tag fmt t =
  pp_print_string fmt
    (if t = tag_true then "True" else if t = tag_false then "False" else t)

(** Printing function for machine type constants. For the moment,
    arrays are not supported.

    @param fmt the formater to use
    @param c the constant to print
 **)
let pp_ada_const fmt c =
  match c with
  | Const_int i                     -> pp_print_int fmt i
  | Const_real (c, e, s)            ->
      fprintf fmt "%s.0*1.0e-%i" (Num.string_of_num c) e
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
    Format.fprintf fmt "((not %a) /= (not %a))" pp_value v1 pp_value v2
  | "/", [v1; v2]    -> pp_div pp_value v1 v2 fmt
  | "&&", [v1; v2]    ->
    Format.fprintf fmt "(%a %s %a)" pp_value v1 "and then" pp_value v2
  | "||", [v1; v2]    ->
    Format.fprintf fmt "(%a %s %a)" pp_value v1 "or else" pp_value v2
  | "!=", [v1; v2]    ->
    Format.fprintf fmt "(%a %s %a)" pp_value v1 "/=" pp_value v2
  | op, [v1; v2]     ->
    Format.fprintf fmt "(%a %s %a)" pp_value v1 op pp_value v2
  | op, [v1] when  List.mem_assoc ident ada_supported_funs ->
    let pkg, name = try List.assoc ident ada_supported_funs
      with Not_found -> assert false in
    let pkg = pkg^(if String.equal pkg "" then "" else ".") in
      Format.fprintf fmt "%s%s(%a)" pkg name pp_value v1
  | fun_name, _      ->
    (Format.eprintf "internal compilation error: basic function %s@." fun_name; assert false)

(** Printing function for values.

    @param m the machine to know the state variable
    @param fmt the formater to use
    @param value the value to print. Should be a
           {!type:Machine_code_types.value_t} value
 **)
let rec pp_value m fmt value =
  match value.value_desc with
  | Cst c             -> pp_ada_const fmt c
  | Var var      -> pp_access_var m fmt var
  | Fun (f_ident, vl) -> pp_basic_lib_fun (pp_value m) f_ident fmt vl
  | _                 ->
    raise (Ada_not_supported
             "unsupported: Ada_backend.adb.pp_value does not support this value type")


(** Print the filename of a machine package.
   @param extension the extension to append to the package name
   @param fmt the formatter
   @param machine the machine corresponding to the package
**)
let pp_machine_filename extension fmt machine =
  pp_filename extension fmt (pp_package_name machine)

let pp_main_filename fmt _ = pp_filename "adb" fmt pp_main_procedure_name


(** Print the declaration of a state element of a subinstance of a machine.
   @param machine the machine
   @param fmt the formater to print on
   @param substitution correspondance between polymorphic type id and their instantiation
   @param ident the identifier of the subinstance
   @param submachine the submachine of the subinstance
**)
let build_pp_state_decl_from_subinstance (name, (substitution, machine)) =
  let pp_package = pp_package_name_with_polymorphic substitution machine in
  let pp_type = pp_package_access (pp_package, pp_state_type) in
  let pp_name fmt = pp_clean_ada_identifier fmt name in
  (AdaNoMode, pp_name, pp_type)

(** Print variable declaration for a local state variable
   @param fmt the formater to print on
   @param mode input/output mode of the parameter
**)
let build_pp_state_decl mode =
  (mode, pp_state_name, pp_state_type)

let build_pp_var_decl mode var =
  let pp_name = function fmt -> pp_var_name fmt var in
  let pp_type = function fmt -> pp_var_type fmt var in
  (mode, pp_name, pp_type)

let build_pp_var_decl_local var =
  AdaLocalVar (build_pp_var_decl AdaNoMode var)

let build_pp_var_decl_step_input mode m =
  if m.mstep.step_inputs=[] then [] else
    [List.map (build_pp_var_decl mode) m.mstep.step_inputs]

let build_pp_var_decl_step_output mode m =
  if m.mstep.step_outputs=[] then [] else
    [List.map (build_pp_var_decl mode) m.mstep.step_outputs]

let build_pp_var_decl_static mode m =
  if m.mstatic=[] then [] else
    [List.map (build_pp_var_decl mode) m.mstatic]

let build_pp_arg_step m =
  (if is_machine_statefull m then [[build_pp_state_decl AdaInOut]] else [])
    @ (build_pp_var_decl_step_input AdaIn m)
    @ (build_pp_var_decl_step_output AdaOut m)

let build_pp_arg_reset m =
  (if is_machine_statefull m then [[build_pp_state_decl AdaOut]] else [])
    @ (build_pp_var_decl_static AdaIn m)
