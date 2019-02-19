open Format

open Machine_code_types
open Lustre_types
open Corelang
open Machine_code_common

(** All the pretty print functions common to the ada backend **)


(* Misc pretty print functions *)

(** Print a cleaned an identifier for ada exportation : Ada names must not start by an
    underscore and must not contain a double underscore
   @param var name to be cleaned*)
let pp_clean_ada_identifier fmt name =
  let base_size = String.length name in
  assert(base_size > 0);
  let rec remove_double_underscore s = function
    | i when i == String.length s - 1 -> s
    | i when String.get s i == '_' && String.get s (i+1) == '_' ->
        remove_double_underscore (sprintf "%s%s" (String.sub s 0 i) (String.sub s (i+1) (String.length s-i-1))) i
    | i -> remove_double_underscore s (i+1)
  in
  let name = remove_double_underscore name 0 in
  let prefix = if String.length name != base_size
                  || String.get name 0 == '_' then
                  "ada"
               else
                  ""
  in
  fprintf fmt "%s%s" prefix name


(* Package pretty print functions *)

(** Print the name of a package associated to a machine.
   @param fmt the formater to print on
   @param machine the machine
**)
let pp_package_name fmt node =
    fprintf fmt "%a" pp_clean_ada_identifier node.node_id

(** Print the ada package introduction sentence it can be used for body and
declaration. Boolean parameter body should be true if it is a body delcaration.
   @param fmt the formater to print on
   @param fmt the formater to print on
   @param machine the machine
**)
let pp_begin_package body fmt machine =
  fprintf fmt "package %s%a is"
    (if body then "body " else "")
    pp_package_name machine.mname

(** Print the ada package conclusion sentence.
   @param fmt the formater to print on
   @param machine the machine
**)
let pp_end_package fmt machine =
  fprintf fmt "end %a" pp_package_name machine.mname

(** Print the access of an item from an other package.
   @param fmt the formater to print on
   @param package the package to use
   @param item the item which is accessed
**)
let pp_package_access fmt (package, item) =
  fprintf fmt "%t.%t" package item

(** Print the name of the main procedure.
   @param fmt the formater to print on
   @param main_machine the machine associated to the main node
**)
let pp_main_procedure_name main_machine fmt =
  fprintf fmt "main"

(** Print the name of the main ada file.
   @param fmt the formater to print on
   @param main_machine the machine associated to the main node
**)
let pp_main_filename fmt main_machine =
  fprintf fmt "%t.adb" (pp_main_procedure_name main_machine)

(** Extract a node from an instance.
   @param instance the instance
**)
let extract_node instance =
  let (_, (node, _)) = instance in
  match node.top_decl_desc with
    | Node nd         -> nd
    | _ -> assert false (*TODO*)

(** Print a with statement to include a node.
   @param fmt the formater to print on
   @param node the node
**)
let pp_with_node fmt node =
  fprintf fmt "private with %a" pp_package_name node


(* Type pretty print functions *)

(** Print a type declaration
   @param fmt the formater to print on
   @param pp_name a format printer which print the type name
   @param pp_value a format printer which print the type definition
**)
let pp_type_decl fmt (pp_name, pp_definition) =
  fprintf fmt "type %t is %t" pp_name pp_definition

(** Print a private type declaration
   @param fmt the formater to print on
   @param pp_name a format printer which print the type name
**)
let pp_private_limited_type_decl fmt pp_name =
  let pp_definition fmt = fprintf fmt "limited private" in
  pp_type_decl fmt (pp_name, pp_definition)

(** Print the type of the state variable.
   @param fmt the formater to print on
**)
let pp_state_type fmt =
  (* Type and variable names live in the same environement in Ada so name of
     this type and of the associated parameter : pp_state_name must be
     different *)
  fprintf fmt "TState"

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

(** Print the type of a variable.
   @param fmt the formater to print on
   @param id the variable
**)
let pp_var_type fmt id =
  (match (Types.repr id.var_type).Types.tdesc with
    | Types.Tbasic Types.Basic.Tint -> pp_integer_type fmt
    | Types.Tbasic Types.Basic.Treal -> pp_float_type fmt
    | Types.Tbasic Types.Basic.Tbool -> pp_boolean_type fmt
    | _ -> eprintf "Type error : %a@." Types.print_ty id.var_type; assert false (*TODO*)
  )


(* Variable pretty print functions *)

(** Represent the possible mode for a type of a procedure parameter **)
type parameter_mode = NoMode | In | Out | InOut

(** Print a parameter_mode.
   @param fmt the formater to print on
   @param mode the modifier
**)
let pp_parameter_mode fmt mode =
  fprintf fmt "%s" (match mode with
                     | NoMode -> ""
                     | In     -> "in"
                     | Out    -> "out"
                     | InOut  -> "in out")

(** Print the name of the state variable.
   @param fmt the formater to print on
**)
let pp_state_name fmt =
  fprintf fmt "state"


(** Print the name of a variable.
   @param fmt the formater to print on
   @param id the variable
**)
let pp_var_name fmt id =
  fprintf fmt "%a" pp_clean_ada_identifier id.var_id

(** Print a variable declaration
   @param mode input/output mode of the parameter
   @param pp_name a format printer wich print the variable name
   @param pp_type a format printer wich print the variable type
   @param fmt the formater to print on
   @param id the variable
**)
let pp_var_decl fmt (mode, pp_name, pp_type) =
  fprintf fmt "%t: %a%s%t"
    pp_name
    pp_parameter_mode mode
    (if mode = NoMode then "" else " ")
    pp_type

(** Print variable declaration for machine variable
   @param mode input/output mode of the parameter
   @param fmt the formater to print on
   @param id the variable
**)
let pp_machine_var_decl mode fmt id =
  let pp_name = function fmt -> pp_var_name fmt id in
  let pp_type = function fmt -> pp_var_type fmt id in
  pp_var_decl fmt (mode, pp_name, pp_type)

(** Print variable declaration for state variable
   @param fmt the formater to print on
   @param mode input/output mode of the parameter
**)
let pp_state_var_decl fmt mode =
  let pp_name = pp_state_name in
  let pp_type = pp_state_type in
  pp_var_decl fmt (mode, pp_name, pp_type)

(** Print the declaration of a state element of node.
   @param instance name of the variable
   @param fmt the formater to print on
   @param instance node
**)
let pp_node_state_decl name fmt node =
  let pp_package fmt = pp_package_name fmt node in
  let pp_type fmt = pp_package_access fmt (pp_package, pp_state_type) in
  let pp_name fmt = pp_clean_ada_identifier fmt name in
  pp_var_decl fmt (NoMode, pp_name, pp_type)


(* Prototype pretty print functions *)

(** Print the name of the reset procedure **)
let pp_reset_procedure_name fmt = fprintf fmt "reset"

(** Print the name of the step procedure **)
let pp_step_procedure_name fmt = fprintf fmt "step"

(** Print the name of the init procedure **)
let pp_init_procedure_name fmt = fprintf fmt "init"

(** Print the name of the clear procedure **)
let pp_clear_procedure_name fmt = fprintf fmt "clear"

(** Print the prototype of a procedure with non input/outputs
   @param fmt the formater to print on
   @param name the name of the procedure
**)
let pp_simple_prototype pp_name fmt =
  fprintf fmt "procedure %t" pp_name

(** Print the prototype of a machine procedure. The first parameter is always
the state, state_modifier specify the modifier applying to it. The next
parameters are inputs and the last parameters are the outputs.
   @param state_mode the input/output mode for the state parameter
   @param input list of the input parameter of the procedure
   @param output list of the output parameter of the procedure
   @param fmt the formater to print on
   @param name the name of the procedure
**)
let pp_base_prototype state_mode input output fmt pp_name =
  fprintf fmt "procedure %t(@[<v>%a%t@[%a@]%t@[%a@])@]"
    pp_name
    pp_state_var_decl state_mode
    (Utils.pp_final_char_if_non_empty ";@," input)
    (Utils.fprintf_list ~sep:";@ " (pp_machine_var_decl In)) input
    (Utils.pp_final_char_if_non_empty ";@," output)
    (Utils.fprintf_list ~sep:";@ " (pp_machine_var_decl Out)) output

(** Print the prototype of the step procedure of a machine.
   @param m the machine
   @param fmt the formater to print on
   @param pp_name name function printer
**)
let pp_step_prototype m fmt =
  pp_base_prototype InOut m.mstep.step_inputs m.mstep.step_outputs fmt pp_step_procedure_name

(** Print the prototype of the reset procedure of a machine.
   @param m the machine
   @param fmt the formater to print on
   @param pp_name name function printer
**)
let pp_reset_prototype m fmt =
  pp_base_prototype InOut m.mstatic [] fmt pp_reset_procedure_name

(** Print the prototype of the init procedure of a machine.
   @param m the machine
   @param fmt the formater to print on
   @param pp_name name function printer
**)
let pp_init_prototype m fmt =
  pp_base_prototype Out m.mstatic [] fmt pp_init_procedure_name

(** Print the prototype of the clear procedure of a machine.
   @param m the machine
   @param fmt the formater to print on
   @param pp_name name function printer
**)
let pp_clear_prototype m fmt =
  pp_base_prototype InOut m.mstatic [] fmt pp_clear_procedure_name


(* Procedure pretty print functions *)

(** Print the definition of a procedure
   @param pp_name the procedure name printer
   @param pp_prototype the prototype printer
   @param pp_instr local var printer
   @param pp_instr instruction printer
   @param fmt the formater to print on
   @param locals locals var list
   @param instrs instructions list
**)
let pp_procedure_definition pp_name pp_prototype pp_local pp_instr fmt (locals, instrs) =
  fprintf fmt "@[<v>%t is%t@[<v>%a%t@]@,begin@,  @[<v>%a%t@]@,end %t@]"
    pp_prototype
    (Utils.pp_final_char_if_non_empty "@,  " locals)
    (Utils.fprintf_list ~sep:";@," pp_local) locals
    (Utils.pp_final_char_if_non_empty ";" locals)
    (Utils.fprintf_list ~sep:";@," pp_instr) instrs
    (Utils.pp_final_char_if_non_empty ";" instrs)
    pp_name
