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

(** Functions printing the .ads file **)
module Main =
struct

(** Print the declaration of a state element of a subinstance of a machine.
   @param machine the machine
   @param fmt the formater to print on
   @param substitution correspondance between polymorphic type id and their instantiation
   @param ident the identifier of the subinstance
   @param submachine the submachine of the subinstance
**)
let pp_machine_subinstance_state_decl fmt (substitution, ident, submachine) =
  pp_node_state_decl substitution ident fmt submachine

(** Print the state record for a machine.
   @param fmt the formater to print on
   @param var_list list of all state var
   @param typed_submachines list of pairs of instantiated types and machine
**)
let pp_state_record_definition fmt (var_list, typed_submachines) =
  fprintf fmt "@,  @[<v>record@,  @[<v>%a%t%a%t@]@,end record@]"
    (Utils.fprintf_list ~sep:";@;" pp_machine_subinstance_state_decl)
    typed_submachines
    (Utils.pp_final_char_if_non_empty ";@," typed_submachines)
    (Utils.fprintf_list ~sep:";@;" (pp_machine_var_decl NoMode))
    var_list
    (Utils.pp_final_char_if_non_empty ";" var_list)

(** Print the declaration for polymorphic types.
   @param fmt the formater to print on
   @param polymorphic_types all the types to print
**)
let pp_generic fmt polymorphic_types =
  let pp_polymorphic_types =
    List.map (fun id fmt -> pp_polymorphic_type fmt id) polymorphic_types in
  if polymorphic_types != [] then
      fprintf fmt "generic@,  @[<v>%a;@]@,"
        (Utils.fprintf_list ~sep:";@," pp_private_limited_type_decl)
        pp_polymorphic_types
  else
    fprintf fmt ""

(** Print instanciation of a generic type in a new statement.
   @param fmt the formater to print on
   @param id id of the polymorphic type
   @param typ the new type
**)
let pp_generic_instanciation fmt (id, typ) =
  fprintf fmt "%a => %a" pp_polymorphic_type id pp_type typ

(** Print a new statement instantiating a generic package.
   @param fmt the formater to print on
   @param substitutions the instanciation substitution
   @param ident the name of the instance, useless in this function
   @param submachine the submachine to instanciate
**)
let pp_new_package fmt (substitutions, ident, submachine) =
  fprintf fmt "package %a is new %a @[<v>(%a)@]"
    (pp_package_name_with_polymorphic substitutions) submachine
    pp_package_name submachine
    (Utils.fprintf_list ~sep:",@," pp_generic_instanciation) substitutions

let pp_eexpr fmt eexpr = fprintf fmt "true"

(** Print a precondition in aspect
   @param fmt the formater to print on
   @param expr the expession to print as pre
**)
let pp_pre fmt expr =
  fprintf fmt "Pre => %a"
    pp_eexpr expr

(** Print a postcondition in aspect
   @param fmt the formater to print on
   @param expr the expession to print as pre
**)
let pp_post fmt expr =
  fprintf fmt "Post => %a"
    pp_eexpr expr

(** Print the declaration of a procedure with a contract
   @param pp_prototype the prototype printer
   @param fmt the formater to print on
   @param contract the contract for the function to declare
**)
let pp_procedure_prototype_contract pp_prototype fmt opt_contract =
  match opt_contract with
    | None -> pp_prototype fmt
    | Some contract -> 
        fprintf fmt "@[<v 2>%t with@,%a,@,%a@]"
          pp_prototype
          (Utils.fprintf_list ~sep:",@," pp_pre) contract.assume
          (Utils.fprintf_list ~sep:",@," pp_post) contract.guarantees

(** Print the prototype with a contract of the reset procedure from a machine.
   @param fmt the formater to print on
   @param machine the machine
**)
let pp_step_prototype_contract fmt m = pp_procedure_prototype_contract
      (pp_step_prototype m)
      fmt
      m.mspec

(** Print the package declaration(ads) of a machine.
   @param fmt the formater to print on
   @param m the machine
**)
let pp_file machines fmt m =
  let submachines = List.map (get_machine machines) m.minstances in
  let names = List.map fst m.minstances in
  let var_list = m.mmemory in
  let typed_submachines = List.map2
    (fun instance submachine ->
      let ident = (fst instance) in
      get_substitution m ident submachine, ident, submachine)
    m.minstances submachines in
  let pp_record fmt =
    pp_state_record_definition fmt (var_list, typed_submachines) in
  let typed_submachines_filtered =
    List.filter (function (l, _, _) -> l != []) typed_submachines in
  let polymorphic_types = find_all_polymorphic_type m in
  fprintf fmt "@[<v>%a%t%a%a@,  @[<v>@,%a;@,@,%t;@,@,%a;@,@,private@,@,%a%t%a;@,@]@,%a;@.@]"
    
    (* Include all the subinstance*)
    (Utils.fprintf_list ~sep:";@," pp_with_machine) submachines
    (Utils.pp_final_char_if_non_empty ";@,@," submachines)
    
    pp_generic polymorphic_types
    
    (*Begin the package*)
    (pp_begin_package false) m
    
    (*Declare the state type*)
    pp_private_limited_type_decl pp_state_type
    
    (*Declare the reset procedure*)
    (pp_reset_prototype m)
    
    (*Declare the step procedure*)
    pp_step_prototype_contract m
    
    (*Instantiate the polymorphic type that need to be instantiate*)
    (Utils.fprintf_list ~sep:";@," pp_new_package) typed_submachines_filtered
    (Utils.pp_final_char_if_non_empty ";@,@," typed_submachines_filtered)
    
    (*Define the state type*)
    pp_type_decl (pp_state_type, pp_record)
    
    (*End the package*)
    pp_end_package m

end
