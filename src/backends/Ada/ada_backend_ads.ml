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
let pp_machine_subinstance_state_decl fmt (ident, (substitution, submachine)) =
  pp_node_state_decl substitution ident fmt submachine

(** Print the state record for a machine.
   @param fmt the formater to print on
   @param var_list list of all state var
   @param typed_instances list typed instances
**)
let pp_state_record_definition fmt (var_list, typed_instances) =
  fprintf fmt "@,  @[<v>record@,  @[<v>%a%t%t%a%t@]@,end record@]"
    (Utils.fprintf_list ~sep:";@;" pp_machine_subinstance_state_decl)
    typed_instances
    (Utils.pp_final_char_if_non_empty ";" typed_instances)
    (fun fmt -> if var_list!=[] && typed_instances!= [] then fprintf fmt "@,@," else fprintf fmt "")
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
   @param machine the machine to instanciate
**)
let pp_new_package fmt (substitutions, machine) =
  fprintf fmt "package %a is new %a @[<v>(%a)@]"
    (pp_package_name_with_polymorphic substitutions) machine
    pp_package_name machine
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
        fprintf fmt "@[<v 2>%t with@,%a%t%a@]"
          pp_prototype
          (Utils.fprintf_list ~sep:",@," pp_pre) contract.assume
          (Utils.pp_final_char_if_non_empty ",@," contract.assume)
          (Utils.fprintf_list ~sep:",@," pp_post) contract.guarantees

(** Print the prototype with a contract of the reset procedure from a machine.
   @param fmt the formater to print on
   @param machine the machine
**)
let pp_step_prototype_contract fmt m = pp_procedure_prototype_contract
      (pp_step_prototype m)
      fmt
      m.mspec

(** Remove duplicates from a list according to a given predicate.
   @param eq the predicate defining equality
   @param l the list to parse
**)
let remove_duplicates eq l =
  let aux l x = if List.exists (eq x) l then l else x::l in
  List.fold_left aux [] l


(** Compare two typed machines.
**)
let eq_typed_machine (subst1, machine1) (subst2, machine2) =
  (String.equal machine1.mname.node_id machine2.mname.node_id) &&
  (List.for_all2 (fun a b -> pp_eq_type (snd a) (snd b)) subst1 subst2)


(** Print the package declaration(ads) of a machine.
  It requires the list of all typed instance.
  A typed submachine is a (ident, typed_machine) with
    - ident: the name 
    - typed_machine: a (substitution, machine) with
      - machine: the submachine struct
      - substitution the instanciation of all its polymorphic types.
   @param fmt the formater to print on
   @param typed_submachines list of all typed submachines of this machine
   @param m the machine
**)
let pp_file fmt (typed_submachines, m) =
  let typed_machines = snd (List.split typed_submachines) in
  let typed_machines_set = remove_duplicates eq_typed_machine typed_machines in
  
  let machines_to_import = snd (List.split typed_machines_set) in

  let polymorphic_types = find_all_polymorphic_type m in
  
  let typed_machines_to_instanciate =
    List.filter (fun (l, _) -> l != []) typed_machines_set in

  let typed_instances = List.filter is_submachine_statefull typed_submachines in
  
  let pp_record fmt =
    pp_state_record_definition fmt (m.mmemory, typed_instances) in

  let pp_state_decl_and_reset fmt = fprintf fmt "%a;@,@,%t;@,@,"
    (*Declare the state type*)
    pp_private_limited_type_decl pp_state_type
    (*Declare the reset procedure*)
    (pp_reset_prototype m)
  in

  let pp_private_section fmt = fprintf fmt "@,private@,@,%a%t%a;@,"
    (*Instantiate the polymorphic type that need to be instantiated*)
    (Utils.fprintf_list ~sep:";@," pp_new_package) typed_machines_to_instanciate
    (Utils.pp_final_char_if_non_empty ";@,@," typed_machines_to_instanciate)
    (*Define the state type*)
    pp_type_decl (pp_state_type, pp_record)
  in
  
  let pp_ifstatefull fmt pp =
    if is_machine_statefull m then
      fprintf fmt "%t" pp
    else
      fprintf fmt ""
  in
  
  fprintf fmt "@[<v>%a%t%a%a@,  @[<v>@,%a%a;@,%a@]@,%a;@.@]"
    
    (* Include all the subinstance package*)
    (Utils.fprintf_list ~sep:";@," pp_with_machine) machines_to_import
    (Utils.pp_final_char_if_non_empty ";@,@," machines_to_import)
    
    pp_generic polymorphic_types
    
    (*Begin the package*)
    (pp_begin_package false) m

    pp_ifstatefull pp_state_decl_and_reset
    
    (*Declare the step procedure*)
    pp_step_prototype_contract m
    
    (*Print the private section*)
    pp_ifstatefull pp_private_section
    
    (*End the package*)
    pp_end_package m

end
