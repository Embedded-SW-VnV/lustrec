open Format

(** Represent the possible mode for a type of a procedure parameter **)
type parameter_mode = AdaNoMode | AdaIn | AdaOut | AdaInOut

type kind_def = AdaType | AdaProcedure | AdaFunction | AdaPackageDecl | AdaPackageBody

type visibility = AdaNoVisibility | AdaPrivate | AdaLimitedPrivate

type printer = Format.formatter -> unit

type ada_with = (bool * (printer list) * (printer list)) option

type ada_var_decl = parameter_mode * printer * printer * ada_with

type ada_local_decl =
  | AdaLocalVar of ada_var_decl
  | AdaLocalPackage of (printer * printer * ((printer*printer) list))

type def_content =
  | AdaNoContent
  | AdaPackageContent of printer
  | AdaSimpleContent of printer
  | AdaVisibilityDefinition of visibility
  | AdaProcedureContent of ((ada_local_decl list list) * (printer list))
  | AdaRecord of ((ada_var_decl list) list)
  | AdaPackageInstanciation of (printer * (printer * printer) list)

(** Print a parameter_mode.
   @param fmt the formater to print on
   @param mode the modifier
**)
let pp_parameter_mode fmt mode =
  fprintf fmt "%s" (match mode with
                     | AdaNoMode -> ""
                     | AdaIn     -> "in"
                     | AdaOut    -> "out"
                     | AdaInOut  -> "in out")

let pp_kind_def fmt kind_def =
  fprintf fmt "%s" (match kind_def with
                     | AdaType        -> "type"
                     | AdaProcedure   -> "procedure"
                     | AdaFunction    -> "function"
                     | AdaPackageDecl -> "package"
                     | AdaPackageBody -> "package body")

let pp_visibility fmt visibility =
  fprintf fmt "%s" (match visibility with
                     | AdaNoVisibility     -> ""
                     | AdaPrivate          -> "private"
                     | AdaLimitedPrivate   -> "limited private")

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

let pp_group ~sep:sep pp_list fmt =
  assert(pp_list != []);
  fprintf fmt "@[%a@]"
    (Utils.fprintf_list ~sep:sep (fun fmt pp->pp fmt)) pp_list

let pp_args ~sep:sep fmt = function
  | [] -> fprintf fmt ""
  | args -> fprintf fmt " (@[<v>%a)@]" (Utils.fprintf_list ~sep:sep (fun fmt pp->pp fmt)) args

let pp_block fmt pp_item_list =
  fprintf fmt "%t@[<v>%a@]%t"
    (Utils.pp_final_char_if_non_empty "  " pp_item_list)
    (Utils.fprintf_list ~sep:";@," (fun fmt pp -> pp fmt)) pp_item_list
    (Utils.pp_final_char_if_non_empty ";@," pp_item_list)


let pp_ada_with fmt = function
  | None -> fprintf fmt ""
  | Some (ghost, pres, posts) ->
      assert(ghost || (pres != []) || (posts != []));
      let contract = pres@posts in
      let pp_ghost fmt = if not ghost then fprintf fmt "" else
        fprintf fmt " Ghost%t" (Utils.pp_final_char_if_non_empty ",@," contract)
      in
      let pp_aspect aspect fmt pps = if pps = [] then fprintf fmt "" else
        fprintf fmt "%s => %t" aspect (pp_group ~sep:"@,and " pps)
      in
      let pp_contract fmt = if contract = [] then fprintf fmt "" else
        let sep = if pres != [] && posts != [] then ",@," else "" in
        fprintf fmt "@,  @[<v>%a%s%a@]"
          (pp_aspect "Pre") pres
          sep
          (pp_aspect "Post") posts
      in
      fprintf fmt " with%t%t"
        pp_ghost
        pp_contract

(** Print instanciation of a generic type in a new statement.
   @param fmt the formater to print on
   @param id id of the polymorphic type
   @param typ the new type
**)
let pp_generic_instanciation (pp_name, pp_type) fmt =
  fprintf fmt "%t => %t" pp_name pp_type

(** Print a variable declaration with mode
   @param mode input/output mode of the parameter
   @param pp_name a format printer wich print the variable name
   @param pp_type a format printer wich print the variable type
   @param fmt the formater to print on
   @param id the variable
**)
let pp_var_decl (mode, pp_name, pp_type, with_statement) fmt =
  fprintf fmt "%t: %a%s%t%a"
    pp_name
    pp_parameter_mode mode
    (if mode = AdaNoMode then "" else " ")
    pp_type
    pp_ada_with with_statement

let apply_var_decl_lists var_list =
  List.map (fun l-> List.map pp_var_decl l) var_list

let pp_generic fmt = function
    | [] -> fprintf fmt ""
    | l -> fprintf fmt "generic@,%a" pp_block l

let pp_opt intro fmt = function
  | None -> fprintf fmt ""
  | Some pp -> fprintf fmt " %s %t" intro pp

let rec pp_local local fmt =
  match local with
    | AdaLocalVar var -> pp_var_decl var fmt
    | AdaLocalPackage (pp_name, pp_base_name, instanciations) ->
        pp_package_instanciation pp_name pp_base_name fmt instanciations
and pp_content pp_name fmt = function
  | AdaNoContent ->
      fprintf fmt ""
  | AdaVisibilityDefinition visbility ->
      fprintf fmt " is %a" pp_visibility visbility
  | AdaPackageContent pp_package ->
      fprintf fmt " is@,  @[<v>%t;@]@,end %t" pp_package pp_name
  | AdaSimpleContent pp_content ->
      fprintf fmt " is@,  @[<v 2>(%t)@]" pp_content
  | AdaProcedureContent (local_list, pp_instr_list) ->
      fprintf fmt " is@,%abegin@,%aend %t"
        pp_block (List.map (fun l -> pp_group ~sep:";@;" (List.map pp_local l)) local_list)
        pp_block pp_instr_list
        pp_name
  | AdaRecord var_list ->
      assert(var_list != []);
      let pp_lists = apply_var_decl_lists var_list in
      fprintf fmt " is@,  @[<v>record@,  @[<v>%a@]@,end record@]"
        pp_block (List.map (pp_group ~sep:";@;") pp_lists)
  | AdaPackageInstanciation (pp_name, instanciations) ->
      fprintf fmt " is new %t%a"
        pp_name
        (pp_args ~sep:",@,") (List.map pp_generic_instanciation instanciations)
and pp_def fmt (pp_generics, kind_def, pp_name, args, pp_type_opt, content, pp_with_opt) =
  let pp_arg_lists = apply_var_decl_lists args in
  fprintf fmt "%a%a %t%a%a%a%a"
    pp_generic pp_generics
    pp_kind_def kind_def
    pp_name
    (pp_args ~sep:";@,") (List.map (pp_group ~sep:";@,") pp_arg_lists)
    (pp_opt "return") pp_type_opt
    (pp_content pp_name) content
    pp_ada_with pp_with_opt
and pp_package_instanciation pp_name pp_base_name fmt instanciations =
  pp_def fmt ([], AdaPackageDecl, pp_name, [], None, (AdaPackageInstanciation (pp_base_name, instanciations)), None)

(** Print the ada package introduction sentence it can be used for body and
declaration. Boolean parameter body should be true if it is a body delcaration.
   @param fmt the formater to print on
   @param fmt the formater to print on
   @param machine the machine
**)
let pp_package pp_name pp_generics body fmt pp_content =
  let kind = if body then AdaPackageBody else AdaPackageDecl in
  pp_def fmt (pp_generics, kind, pp_name, [], None, (AdaPackageContent pp_content), None)

(** Print a new statement instantiating a generic package.
   @param fmt the formater to print on
   @param substitutions the instanciation substitution
   @param machine the machine to instanciate
**)

(** Print a type declaration
   @param fmt the formater to print on
   @param pp_name a format printer which print the type name
   @param pp_value a format printer which print the type definition
**)
let pp_type_decl pp_name visibility fmt =
  pp_def fmt ([], AdaType, pp_name, [], None, AdaVisibilityDefinition visibility, None)

let pp_record pp_name fmt var_lists =
  pp_def fmt ([], AdaType, pp_name, [], None, AdaRecord var_lists, None)

let pp_procedure pp_name args pp_with_opt fmt content =
  pp_def fmt ([], AdaProcedure, pp_name, args, None, content, pp_with_opt)

let pp_predicate pp_name args fmt content_opt =
  let rec quantify pp_content = function
    | [] -> pp_content
    | (pp_var, pp_type)::q -> fun fmt ->
      fprintf fmt "for some %t in %t => (@,  @[<v>%t@])" pp_var pp_type (quantify pp_content q)
  in
  let content, with_st = match content_opt with
    | Some (locals, booleans) -> AdaSimpleContent (quantify (fun fmt -> Utils.fprintf_list ~sep:"@;and " (fun fmt pp->pp fmt) fmt booleans) locals), None
    | None -> AdaNoContent, Some (true, [], [])
  in
  pp_def fmt ([], AdaFunction, pp_name, args, Some pp_boolean_type, content, with_st)




(** Print a cleaned an identifier for ada exportation : Ada names must not start by an
    underscore and must not contain a double underscore
   @param var name to be cleaned*)
let pp_clean_ada_identifier fmt name =
  let reserved_words = ["abort"; "else"; "new"; "return"; "boolean"; "integer";
                        "abs"; "elsif"; "not"; "reverse"; "abstract"; "end";
                        "null"; "accept"; "entry"; "select"; "access";
                        "exception"; "of"; "separate"; "aliased"; "exit";
                        "or"; "some"; "all"; "others"; "subtype"; "and";
                        "for"; "out"; "synchronized"; "array"; "function";
                        "overriding"; "at"; "tagged"; "generic"; "package";
                        "task"; "begin"; "goto"; "pragma"; "terminate";
                        "body"; "private"; "then"; "if"; "procedure"; "type";
                        "case"; "in"; "protected"; "constant"; "interface";
                        "until"; "is"; "raise"; "use"; "declare"; "	range";
                        "delay"; "limited"; "record"; "when"; "delta"; "loop";
                        "rem"; "while"; "digits"; "renames"; "with"; "do";
                        "mod"; "requeue"; "xor"; "float"] in
  let base_size = String.length name in
  assert(base_size > 0);
  let rec remove_double_underscore s = function
    | i when i == String.length s - 1 -> s
    | i when String.get s i == '_' && String.get s (i+1) == '_' ->
        remove_double_underscore (sprintf "%s%s" (String.sub s 0 i) (String.sub s (i+1) (String.length s-i-1))) i
    | i -> remove_double_underscore s (i+1)
  in
  let name = if String.get name (base_size-1) == '_' then name^"ada" else name in
  let name = remove_double_underscore name 0 in
  let prefix = if String.length name != base_size
                  || String.get name 0 == '_' 
                  || List.exists (String.equal (String.lowercase_ascii name)) reserved_words then
                  "ada"
               else
                  ""
  in
  fprintf fmt "%s%s" prefix name

(** Print the access of an item from an other package.
   @param fmt the formater to print on
   @param package the package to use
   @param item the item which is accessed
**)
let pp_package_access (pp_package, pp_item) fmt =
  fprintf fmt "%t.%t" pp_package pp_item

let pp_with visibility fmt pp_pakage_name =
  fprintf fmt "%a with %t" pp_visibility visibility pp_pakage_name

(** Print a one line comment with the final new line character to avoid
      commenting anything else.
   @param fmt the formater to print on
   @param s the comment without newline character
**)
let pp_oneline_comment fmt s =
  assert (not (String.contains s '\n'));
  fprintf fmt "-- %s@," s

let pp_call fmt (pp_name, args) =
  fprintf fmt "%t%a"
    pp_name
    (pp_args ~sep:",@ ") (List.map (pp_group ~sep:",@,") args)


(** Print the complete name of variable.
   @param m the machine to check if it is memory
   @param fmt the formater to print on
   @param var the variable
**)
let pp_access pp_state pp_var fmt =
  fprintf fmt "%t.%t" pp_state pp_var

let pp_old pp fmt = fprintf fmt "%t'Old" pp

