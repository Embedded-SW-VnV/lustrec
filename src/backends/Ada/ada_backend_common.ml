open Format

open Machine_code_types
open Lustre_types
open Corelang
open Machine_code_common

(** Exception for unsupported features in Ada backend **)
exception Ada_not_supported of string

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

(** Encapsulate a pretty print function to lower case its result when applied
   @param pp the pretty print function
   @param fmt the formatter
   @param arg the argument of the pp function
**)
let pp_lowercase pp fmt =
  let str = asprintf "%t" pp in
  fprintf fmt "%s" (String. lowercase_ascii str)

(** Print a filename by lowercasing the base and appending an extension.
   @param extension the extension to append to the package name
   @param fmt the formatter
   @param pp_name the file base name printer
**)
let pp_filename extension fmt pp_name =
  fprintf fmt "%t.%s"
    (pp_lowercase pp_name)
    extension


(* Package pretty print functions *)

(** Print the name of the arrow package.
   @param fmt the formater to print on
**)
let pp_arrow_package_name fmt = fprintf fmt "Arrow"

(** Print the name of a package associated to a node.
   @param fmt the formater to print on
   @param machine the machine
**)
let pp_package_name_from_node fmt node =
  if String.equal Arrow.arrow_id node.node_id then
      fprintf fmt "%t" pp_arrow_package_name
  else
      fprintf fmt "%a" pp_clean_ada_identifier node.node_id

(** Print the name of a package associated to a machine.
   @param fmt the formater to print on
   @param machine the machine
**)
let pp_package_name fmt machine =
  pp_package_name_from_node fmt machine.mname

(** Print the ada package introduction sentence it can be used for body and
declaration. Boolean parameter body should be true if it is a body delcaration.
   @param fmt the formater to print on
   @param fmt the formater to print on
   @param machine the machine
**)
let pp_begin_package body fmt machine =
  fprintf fmt "package %s%a is"
    (if body then "body " else "")
    pp_package_name machine

(** Print the ada package conclusion sentence.
   @param fmt the formater to print on
   @param machine the machine
**)
let pp_end_package fmt machine =
  fprintf fmt "end %a" pp_package_name machine

(** Print the access of an item from an other package.
   @param fmt the formater to print on
   @param package the package to use
   @param item the item which is accessed
**)
let pp_package_access fmt (package, item) =
  fprintf fmt "%t.%t" package item

(** Print the name of the main procedure.
   @param fmt the formater to print on
**)
let pp_main_procedure_name fmt =
  fprintf fmt "main"

(** Print a with statement to include a package.
   @param fmt the formater to print on
   @param pp_pakage_name the package name printer
**)
let pp_with fmt pp_pakage_name =
  fprintf fmt "with %t" pp_pakage_name

(** Print a with statement to include a machine.
   @param fmt the formater to print on
   @param machine the machine
**)
let pp_with_machine fmt machine =
  fprintf fmt "private with %a" pp_package_name machine

(** Extract a node from an instance.
   @param instance the instance
**)
let extract_node instance =
  let (_, (node, _)) = instance in
  match node.top_decl_desc with
    | Node nd         -> nd
    | _ -> assert false (*TODO*)

(** Extract from a machine list the one corresponding to the given instance.
   @param machines list of all machines
   @param instance instance of a machine
   @return the machine corresponding to hte given instance
**)
let get_machine machines instance =
    let id = (extract_node instance).node_id in
    List.find  (function m -> m.mname.node_id=id) machines


(* Type pretty print functions *)

(** Print a type declaration
   @param fmt the formater to print on
   @param pp_name a format printer which print the type name
   @param pp_value a format printer which print the type definition
**)
let pp_type_decl fmt (pp_name, pp_definition) =
  fprintf fmt "type %t is %t" pp_name pp_definition

(** Print a limited private type declaration
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

(** Print the type of a polymorphic type.
   @param fmt the formater to print on
   @param id the id of the polymorphic type
**)
let pp_polymorphic_type fmt id =
  fprintf fmt "T_%i" id

(** Print a type.
   @param fmt the formater to print on
   @param type the type
**)
let pp_type fmt typ = 
  (match (Types.repr typ).Types.tdesc with
    | Types.Tbasic Types.Basic.Tint  -> pp_integer_type fmt
    | Types.Tbasic Types.Basic.Treal -> pp_float_type fmt
    | Types.Tbasic Types.Basic.Tbool -> pp_boolean_type fmt
    | Types.Tunivar _                -> pp_polymorphic_type fmt typ.tid
    | Types.Tconst _                 -> eprintf "Tconst@."; assert false (*TODO*)
    | Types.Tclock _                 -> eprintf "Tclock@."; assert false (*TODO*)
    | Types.Tarrow _                 -> eprintf "Tarrow@."; assert false (*TODO*)
    | Types.Ttuple l                 -> eprintf "Ttuple %a @." (Utils.fprintf_list ~sep:" " Types.print_ty) l; assert false (*TODO*)
    | Types.Tenum _                  -> eprintf "Tenum@.";  assert false (*TODO*)
    | Types.Tstruct _                -> eprintf "Tstruct@.";assert false (*TODO*)
    | Types.Tarray _                 -> eprintf "Tarray@."; assert false (*TODO*)
    | Types.Tstatic _                -> eprintf "Tstatic@.";assert false (*TODO*)
    | Types.Tlink _                  -> eprintf "Tlink@.";  assert false (*TODO*)
    | Types.Tvar _                   -> eprintf "Tvar@.";   assert false (*TODO*)
    | _ -> eprintf "Type error : %a@." Types.print_ty typ; assert false (*TODO*)
  )

(** Print the type of a variable.
   @param fmt the formater to print on
   @param id the variable
**)
let pp_var_type fmt id = 
  pp_type fmt id.var_type

(** Extract all the inputs and outputs.
   @param machine the machine
   @return a list of all the var_decl of a macine
**)
let get_all_vars_machine m =
  m.mmemory@m.mstep.step_inputs@m.mstep.step_outputs@m.mstatic

(** Check if a type is polymorphic.
   @param typ the type
   @return true if its polymorphic
**)
let is_Tunivar typ = (Types.repr typ).tdesc == Types.Tunivar

(** Find all polymorphic type : Types.Tunivar in a machine.
   @param machine the machine
   @return a list of id corresponding to polymorphic type
**)
let find_all_polymorphic_type m =
  let vars = get_all_vars_machine m in
  let extract id = id.var_type.tid in
  let polymorphic_type_vars =
    List.filter (function x-> is_Tunivar x.var_type) vars in
  List.sort_uniq (-) (List.map extract polymorphic_type_vars)

(** Print a package name with polymorphic types specified.
   @param substitution correspondance between polymorphic type id and their instantiation
   @param fmt the formater to print on
   @param machine the machine
**)
let pp_package_name_with_polymorphic substitution fmt machine =
  let polymorphic_types = find_all_polymorphic_type machine in
  assert(List.length polymorphic_types = List.length substitution);
  let substituion = List.sort_uniq (fun x y -> fst x - fst y) substitution in
  assert(List.for_all2 (fun poly1 (poly2, _) -> poly1 = poly2)
            polymorphic_types substituion);
  let instantiated_types = snd (List.split substitution) in
  fprintf fmt "%a%t%a"
    pp_package_name machine
    (Utils.pp_final_char_if_non_empty "_" instantiated_types)
    (Utils.fprintf_list ~sep:"_" pp_type) instantiated_types


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

(** Print variable declaration for a local state variable
   @param fmt the formater to print on
   @param mode input/output mode of the parameter
**)
let pp_state_var_decl fmt mode =
  let pp_name = pp_state_name in
  let pp_type = pp_state_type in
  pp_var_decl fmt (mode, pp_name, pp_type)

(** Print the declaration of a state element of a machine.
   @param substitution correspondance between polymorphic type id and their instantiation
   @param name name of the variable
   @param fmt the formater to print on
   @param machine the machine
**)
let pp_node_state_decl substitution name fmt machine =
  let pp_package fmt = pp_package_name_with_polymorphic substitution fmt machine in
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


(* Functions which computes the substitution for polymorphic type *)
(** Find a submachine step call in a list of instructions.
    @param ident submachine instance ident
    @param instr_list List of instruction sto search
    @return a list of pair containing input types and output types for each step call found
**)
let rec find_submachine_step_call ident instr_list =
  let search_instr instruction = 
    match instruction.instr_desc with
      | MStep (il, i, vl) when String.equal i ident -> [
        (List.map (function x-> x.value_type) vl,
            List.map (function x-> x.var_type) il)]
      | MBranch (_, l) -> List.flatten
          (List.map (function x, y -> find_submachine_step_call ident y) l)
      | _ -> []
  in
  List.flatten (List.map search_instr instr_list)

(** Check that two types are the same.
   @param t1 a type
   @param t2 an other type
   @param return true if the two types are Tbasic or Tunivar and equal
**)
let rec check_type_equal (t1:Types.type_expr) (t2:Types.type_expr) =
  match (Types.repr t1).Types.tdesc, (Types.repr t2).Types.tdesc with
    | Types.Tbasic x, Types.Tbasic y -> x = y
    | Types.Tunivar,  Types.Tunivar  -> t1.tid = t2.tid
    | Types.Ttuple l, _ -> assert (List.length l = 1); check_type_equal (List.hd l) t2
    | _, Types.Ttuple l -> assert (List.length l = 1); check_type_equal t1 (List.hd l)
    | Types.Tstatic (_, t), _ -> check_type_equal t t2
    | _, Types.Tstatic (_, t) -> check_type_equal t1 t
    | _ -> eprintf "ERROR: %a | %a" pp_type t1 pp_type t2; assert false (* TODO *)

(** Extend a substitution to unify the two given types. Only the
  first type can be polymorphic.
    @param subsitution the base substitution
    @param type_poly the type which can be polymorphic
    @param typ the type to match type_poly with
**)
let unification (substituion:(int*Types.type_expr) list) ((type_poly:Types.type_expr), (typ:Types.type_expr)) =
  assert(not (is_Tunivar typ));
  (* If type_poly is polymorphic *)
  if is_Tunivar type_poly then
    (* If a subsitution exists for it *)
    if List.mem_assoc type_poly.tid substituion then
    begin
      (* We check that the type corresponding to type_poly in the subsitution
         match typ *)
      assert(check_type_equal (List.assoc type_poly.tid substituion) typ);
      (* We return the original substituion, it is already correct *)
      substituion
    end
    (* If type_poly is not in the subsitution *)
    else
      (* We add it to the substituion *)
      (type_poly.tid, typ)::substituion
  (* iftype_poly is not polymorphic *)
  else
  begin
    (* We check that type_poly and typ are the same *)
    assert(check_type_equal type_poly typ);
    (* We return the original substituion, it is already correct *)
    substituion
  end

(** Check that two calls are equal. A call is
  a pair of list of types, the inputs and the outputs.
   @param calls a list of pair of list of types
   @param return true if the two pairs are equal
**)
let check_call_equal (i1, o1) (i2, o2) =
  (List.for_all2 check_type_equal i1 i2)
    && (List.for_all2 check_type_equal i1 i2)

(** Check that all the elements of list of calls are equal to one.
  A call is a pair of list of types, the inputs and the outputs.
   @param call a pair of list of types
   @param calls a list of pair of list of types
   @param return true if all the elements are equal
**)
let check_calls call calls =
  List.for_all (check_call_equal call) calls

(** Extract from a subinstance that can have polymorphic type the instantiation
    of all its polymorphic type instanciation for a given machine. It searches
    the step calls and extract a substitution for all polymorphic type from
    it.
   @param machine the machine which instantiate the subinstance
   @param ident the identifier of the instance which permits to find the step call
   @param submachine the machine corresponding to the subinstance
   @return the correspondance between polymorphic type id and their instantiation
**)
let get_substitution machine ident submachine =
  (* extract the calls to submachines from the machine *)
  let calls = find_submachine_step_call ident machine.mstep.step_instrs in
  (* extract the first call  *)
  let call = match calls with
              (* assume that there is always one call to a subinstance *)
              | []    -> assert(false)
              | h::t  -> h in
  (* assume that all the calls to a subinstance are using the same type *)
  assert(check_calls call calls);
  (* make a list of all types from input and output vars *)
  let call_types = (fst call)@(snd call) in
  (* extract all the input and output vars from the submachine *)
  let machine_vars = submachine.mstep.step_inputs@submachine.mstep.step_outputs in
  (* keep only the type of vars *)
  let machine_types = List.map (function x-> x.var_type) machine_vars in
  (* assume that there is the same numer of input and output in the submachine
      and the call *)
  assert (List.length machine_types = List.length call_types);
  (* Unify the two lists of types *)
  let substitution = List.fold_left unification [] (List.combine machine_types call_types) in
  (* Assume that our substitution match all the possible
       polymorphic type of the node *)
  let polymorphic_types = find_all_polymorphic_type submachine in
  assert (List.length polymorphic_types = List.length substitution);
  assert (List.for_all (function x->List.mem_assoc x substitution) polymorphic_types);
  substitution


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
