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

(** Print name of a node associated to an instance.
   @param fmt the formater to print on
   @param instance the instance
**)
let pp_instance_node_name fmt instance =
  let (_, (node, _)) = instance in
  let node = match node.top_decl_desc with 
              | Node nd         -> nd
              | _ -> assert false (*TODO*) in
  pp_package_name fmt node

(** Print the declaration of a state element of a subinstance of a machine.
   @param fmt the formater to print on
   @param instance the instance
**)
let pp_machine_subinstance_state_decl fmt instance =
  let (name, (node, static)) = instance in
  let pp_package fmt = pp_instance_node_name fmt instance in
  let pp_type fmt = pp_package_access fmt (pp_package, pp_state_type) in
  let pp_name fmt = print_clean_ada_identifier fmt name in
  pp_var_decl fmt (NoMode, pp_name, pp_type)

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

(** Print a with statement to include an instance.
   @param fmt the formater to print on
   @param instance the instance
**)
let pp_with_subinstance fmt instance =
  fprintf fmt "private with %a" pp_instance_node_name instance

(** Print the package declaration(ads) of a machine.
   @param fmt the formater to print on
   @param machine the machine
**)
let print fmt machine =
  (* Take apart the arrow instance from the instance list and transform them
     into simple boolean variable *)
  let extract (instances, arrows) instance =
    let (name, (node, static)) = instance in
    if String.equal (node_name node) Arrow.arrow_id then
      (instances, (dummy_var_decl name Type_predef.type_bool)::arrows)
    else
      (instance::instances, arrows) in
  let instances, arrows = List.fold_left extract ([], []) machine.minstances in
  (* Add the boolean variable reated for arrow instance to the list of all variable *)
  let var_list = arrows@machine.mmemory in
  let pp_record fmt = pp_state_record_definition fmt (var_list, instances) in
  fprintf fmt "@[<v>%a%t@,%a@,  @[<v>@,%a;@,@,%a;@,@,%a;@,@,%a;@,@,%a;@,@,private@,@,%a;@,@]@,%a;@.@]"
    (Utils.fprintf_list ~sep:";@," pp_with_subinstance) instances (* Include all the subinstance*)
    (Utils.pp_final_char_if_non_empty ";@," instances)
    (pp_begin_package false) machine (*Begin the package*)
    pp_private_type_decl pp_state_type (*Declare the state type*)
    pp_init_prototype machine (*Declare the init procedure*)
    pp_step_prototype machine (*Declare the step procedure*)
    pp_reset_prototype machine (*Declare the reset procedure*)
    pp_clear_prototype machine (*Declare the clear procedure*)
    pp_type_decl (pp_state_type, pp_record) (*Define the state type*)
    pp_end_package machine  (*End the package*)

end
