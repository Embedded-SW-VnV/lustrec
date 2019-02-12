open Format

open Machine_code_types
open Lustre_types
open Corelang
open Machine_code_common

(** All the pretty print functions common to the ada backend **)

(* Package pretty print functions *)

(** Print the name of a package associated to a machine.
   @param fmt the formater to print on
   @param machine the machine
*)
let pp_package_name fmt machine =
  fprintf fmt "%s" machine.mname.node_id

(** Print the ada package introduction sentence it can be used for body and
declaration. Boolean parameter body should be true if it is a body delcaration.
   @param fmt the formater to print on
   @param fmt the formater to print on
   @param machine the machine
*)
let pp_begin_package body fmt machine =
  fprintf fmt "package %s %a is"
    (if body then "body" else "")
    pp_package_name machine

(** Print the ada package conclusion sentence.
   @param fmt the formater to print on
   @param machine the machine
*)
let pp_end_package fmt machine =
  fprintf fmt "end %a;" pp_package_name machine


(* Variable pretty print functions *)

(** Print the name of a variable.
   @param fmt the formater to print on
   @param id the variable
*)
let pp_var_name fmt id =
  fprintf fmt "%s" id.var_id

(** Print the type of a variable.
   @param fmt the formater to print on
   @param id the variable
*)
let pp_var_type fmt id = fprintf fmt
  (match (Types.repr id.var_type).Types.tdesc with
    | Types.Tbasic Types.Basic.Tint -> "int"
    | Types.Tbasic Types.Basic.Treal -> "double"
    | Types.Tbasic Types.Basic.Tbool -> "bool"
    | _ -> eprintf "Type error : %a@." Types.print_ty id.var_type; assert false (*TODO*)
  )


(* Prototype pretty print functions *)

type prototype_modifiers = In | Out

(** Print a prototype_modifiers.
   @param fmt the formater to print on
   @param modifier the modifier
*)
let pp_prototype_modifiers fmt modifier =
  fprintf fmt "%s" (match modifier with
                     | In  -> "in"
                     | Out -> "out")

(** Print a variable declaration.
   @param fmt the formater to print on
   @param id the variable
*)
let pp_var_decl fmt id =
  fprintf fmt "type %a is %a;"
    pp_var_name id
    pp_var_type id

(** Print the parameter of a prototype, a list of modifier(eg. in or out)
  can be given to specify the type.
   @param modifiers list of the modifiers for this parameter
   @param fmt the formater to print on
   @param id the variable
*)
let pp_parameter modifiers fmt id =
  fprintf fmt "%a: %a %a"
    pp_var_name id
    (Utils.fprintf_list ~sep:"@ " pp_prototype_modifiers) modifiers
    pp_var_type id

(** Print the prototype of a procedure
   @param fmt the formater to print on
   @param name the name of the procedure
   @param input list of the input parameter of the procedure
   @param output list of the output parameter of the procedure
*)
let pp_simple_prototype fmt (name, input, output) =
  fprintf fmt "procedure %s(@[<v>@[%a%t%a@])@]"
    name
    (Utils.fprintf_list ~sep:",@ " (pp_parameter [In])) input
    (Utils.pp_final_char_if_non_empty ",@," input)
    (Utils.fprintf_list ~sep:",@ " (pp_parameter [Out])) output

(** Print the prototype of the init procedure of a machine.
   @param fmt the formater to print on
   @param m the machine
*)
let pp_init_prototype fmt m =
  pp_simple_prototype fmt ("init", m.mstatic, [])

(** Print the prototype of the step procedure of a machine.
   @param fmt the formater to print on
   @param m the machine
*)
let pp_step_prototype fmt m =
  pp_simple_prototype fmt ("step", m.mstep.step_inputs, m.mstep.step_outputs)

(** Print the prototype of the reset procedure of a machine.
   @param fmt the formater to print on
   @param m the machine
*)
let pp_reset_prototype fmt m =
  pp_simple_prototype fmt ("reset", m.mstatic, [])

(** Print the prototype of the clear procedure of a machine.
   @param fmt the formater to print on
   @param m the machine
*)
let pp_clear_prototype fmt m =
  pp_simple_prototype fmt ("clear", m.mstatic, [])
