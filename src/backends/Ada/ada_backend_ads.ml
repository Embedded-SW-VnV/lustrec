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

(** Print a with statement to include an instance.
   @param fmt the formater to print on
   @param instance the instance
**)
let pp_with_subinstance fmt instance =
  pp_with_node fmt (extract_node instance)

(** Print the declaration of a state element of a subinstance of a machine.
   @param fmt the formater to print on
   @param instance the instance
**)
let pp_machine_subinstance_state_decl fmt instance =
  pp_node_state_decl (fst instance) fmt (extract_node instance)

(** Print the state record for a machine.
   @param fmt the formater to print on
   @param machine the machine
**)
let pp_state_record_definition fmt (var_list, instances) =
  fprintf fmt "@,  @[<v>record@,  @[<v>%a%t%a%t@]@,end record@]"
    (Utils.fprintf_list ~sep:";@;" pp_machine_subinstance_state_decl) instances
    (Utils.pp_final_char_if_non_empty ";@," instances)
    (Utils.fprintf_list ~sep:";@;" (pp_machine_var_decl NoMode)) var_list
    (Utils.pp_final_char_if_non_empty ";" var_list)

(** Print the package declaration(ads) of a machine.
   @param fmt the formater to print on
   @param m the machine
**)
let pp_file fmt m =
  (* Take apart the arrow instance from the instance list and transform them
     into simple boolean variable *)
  let extract (instances, arrows) instance =
    let (name, (node, static)) = instance in
    if String.equal (node_name node) Arrow.arrow_id then
      (instances, (dummy_var_decl name Type_predef.type_bool)::arrows)
    else
      (instance::instances, arrows) in
  let instances, arrows = List.fold_left extract ([], []) m.minstances in
  (* Add the boolean variable reated for arrow instance to the list of all variable *)
  let var_list = arrows@m.mmemory in
  let pp_record fmt = pp_state_record_definition fmt (var_list, instances) in
  fprintf fmt "@[<v>%a%t@,%a@,  @[<v>@,%a;@,@,%a;@,@,%a;@,@,%a;@,@,%a;@,@,private@,@,%a;@,@]@,%a;@.@]"
    
    (* Include all the subinstance*)
    (Utils.fprintf_list ~sep:";@," pp_with_subinstance) instances
    (Utils.pp_final_char_if_non_empty ";@," instances)
    
    (*Begin the package*)
    (pp_begin_package false) m
    
    (*Declare the state type*)
    pp_private_type_decl pp_state_type
    
    (*Declare the init procedure*)
    (pp_init_prototype m) pp_init_procedure_name
    
    (*Declare the step procedure*)
    (pp_step_prototype m) pp_step_procedure_name
    
    (*Declare the reset procedure*)
    (pp_reset_prototype m) pp_reset_procedure_name
    
    (*Declare the clear procedure*)
    (pp_clear_prototype m) pp_clear_procedure_name
    
    (*Define the state type*)
    pp_type_decl (pp_state_type, pp_record)
    
    (*End the package*)
    pp_end_package m

end
