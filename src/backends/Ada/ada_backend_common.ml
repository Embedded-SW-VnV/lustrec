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
  fprintf fmt "end %a" pp_package_name machine


(* Type pretty print functions *)

(** Print a type declaration
   @param fmt the formater to print on
   @param pp_name a format printer which print the type name
   @param pp_value a format printer which print the type definition
*)
let pp_type_decl fmt (pp_name, pp_definition) =
  fprintf fmt "type %t is %t" pp_name pp_definition

(** Print a private type declaration
   @param fmt the formater to print on
   @param pp_name a format printer which print the type name
*)
let pp_private_type_decl fmt pp_name =
  let pp_definition fmt = fprintf fmt "private" in
  pp_type_decl fmt (pp_name, pp_definition)

(** Print the type of the state variable.
   @param fmt the formater to print on
*)
let pp_state_type fmt =
  fprintf fmt "TState"

(** Print the type of a variable.
   @param fmt the formater to print on
   @param id the variable
*)
let pp_var_type fmt id = fprintf fmt
  (match (Types.repr id.var_type).Types.tdesc with
    | Types.Tbasic Types.Basic.Tint -> "Integer"
    | Types.Tbasic Types.Basic.Treal -> "Float"
    | Types.Tbasic Types.Basic.Tbool -> "Boolean"
    | _ -> eprintf "Type error : %a@." Types.print_ty id.var_type; assert false (*TODO*)
  )
  

(* Variable pretty print functions *)

(** Represent the possible mode for a type of a procedure parameter **)
type parameter_mode = NoMode | In | Out | InOut

(** Print a parameter_mode.
   @param fmt the formater to print on
   @param mode the modifier
*)
let pp_parameter_mode fmt mode =
  fprintf fmt "%s" (match mode with
                     | NoMode -> ""
                     | In     -> "in"
                     | Out    -> "out"
                     | InOut  -> "in out")

(** Print the name of the state variable.
   @param fmt the formater to print on
*)
let pp_state_name fmt =
  fprintf fmt "state"

(** Print the name of a variable.
   @param fmt the formater to print on
   @param id the variable
*)
let pp_var_name fmt id =
  let base_size = String.length id.var_id in
  assert(base_size > 0);
  let rec remove_double_underscore s = function
    | i when i == String.length s - 1 -> s
    | i when String.get s i == '_' && String.get s (i+1) == '_' ->
        remove_double_underscore (sprintf "%s%s" (String.sub s 0 i) (String.sub s (i+1) (String.length s-i-1))) i
    | i -> remove_double_underscore s (i+1)
  in
  let name = remove_double_underscore id.var_id 0 in
  let prefix = if String.length name == base_size
                  || String.get id.var_id 0 == '_' then
                  "ada"
               else
                  ""
  in
  fprintf fmt "%s%s" prefix name

(** Print a variable declaration
   @param mode input/output mode of the parameter
   @param pp_name a format printer wich print the variable name
   @param pp_type a format printer wich print the variable type
   @param fmt the formater to print on
   @param id the variable
*)
let pp_var_decl fmt (mode, pp_name, pp_type) =
  fprintf fmt "%t: %a %t"
    pp_name
    pp_parameter_mode mode
    pp_type

(** Print variable declaration for machine variable
   @param mode input/output mode of the parameter
   @param fmt the formater to print on
   @param id the variable
*)
let pp_machine_var_decl mode fmt id =
  let pp_name = function fmt -> pp_var_name fmt id in
  let pp_type = function fmt -> pp_var_type fmt id in
  pp_var_decl fmt (mode, pp_name, pp_type)

(** Print variable declaration for state variable
   @param fmt the formater to print on
   @param mode input/output mode of the parameter
*)
let pp_state_var_decl fmt mode =
  let pp_name = pp_state_name in
  let pp_type = pp_state_type in
  pp_var_decl fmt (mode, pp_name, pp_type)


(* Prototype pretty print functions *)

(** Print the name of the init procedure **)
let pp_init_procedure_name fmt = fprintf fmt "init"

(** Print the step of the init procedure **)
let pp_step_procedure_name fmt = fprintf fmt "step"

(** Print the reset of the init procedure **)
let pp_reset_procedure_name fmt = fprintf fmt "reset"

(** Print the clear of the init procedure **)
let pp_clear_procedure_name fmt = fprintf fmt "clear"

(** Print the prototype of a machine procedure. The first parameter is always
the state, state_modifier specify the modifier applying to it. The next
parameters are inputs and the last parameters are the outputs.
   @param fmt the formater to print on
   @param name the name of the procedure
   @param state_mode the input/output mode for the state parameter
   @param input list of the input parameter of the procedure
   @param output list of the output parameter of the procedure
*)
let pp_simple_prototype fmt (pp_name, state_mode, input, output) =
  fprintf fmt "procedure %t(@[<v>%a%t@[%a@]%t@[%a@])@]"
    pp_name
    pp_state_var_decl state_mode
    (Utils.pp_final_char_if_non_empty ";@," input)
    (Utils.fprintf_list ~sep:";@ " (pp_machine_var_decl In)) input
    (Utils.pp_final_char_if_non_empty ";@," output)
    (Utils.fprintf_list ~sep:";@ " (pp_machine_var_decl Out)) output

(** Print the prototype of the init procedure of a machine.
   @param fmt the formater to print on
   @param m the machine
*)
let pp_init_prototype fmt m =
  pp_simple_prototype fmt (pp_init_procedure_name, Out, m.mstatic, [])

(** Print the prototype of the step procedure of a machine.
   @param fmt the formater to print on
   @param m the machine
*)
let pp_step_prototype fmt m =
  pp_simple_prototype fmt (pp_step_procedure_name, InOut, m.mstep.step_inputs, m.mstep.step_outputs)

(** Print the prototype of the reset procedure of a machine.
   @param fmt the formater to print on
   @param m the machine
*)
let pp_reset_prototype fmt m =
  pp_simple_prototype fmt (pp_reset_procedure_name, InOut, m.mstatic, [])

(** Print the prototype of the clear procedure of a machine.
   @param fmt the formater to print on
   @param m the machine
*)
let pp_clear_prototype fmt m =
  pp_simple_prototype fmt (pp_clear_procedure_name, InOut, m.mstatic, [])
