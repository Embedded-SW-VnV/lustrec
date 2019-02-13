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

(** Print a record definition.
   @param fmt the formater to print on
   @param var_list list of machine variable
*)
let pp_record_definition fmt var_list =
  fprintf fmt "@,  @[<v>record@,  @[<v>%a%t@]@,end record@]"
    (Utils.fprintf_list ~sep:";@;" (pp_machine_var_decl NoMode)) var_list
    (Utils.pp_final_char_if_non_empty ";" var_list)

(** Print the package declaration(ads) of a machine.
   @param fmt the formater to print on
   @param machine the machine
*)
let print fmt machine =
  let pp_record fmt = pp_record_definition fmt machine.mmemory in
  fprintf fmt "%a@,  @[<v>@,%a;@,@,%a;@,@,%a;@,@,%a;@,@,%a;@,@,private@,@,%a;@,@]@,%a;@."
    (pp_begin_package false) machine (*Begin the package*)
    pp_private_type_decl pp_state_type (*Declare the state type*)
    pp_init_prototype machine (*Declare the init procedure*)
    pp_step_prototype machine (*Declare the step procedure*)
    pp_reset_prototype machine (*Declare the reset procedure*)
    pp_clear_prototype machine (*Declare the clear procedure*)
    pp_type_decl (pp_state_type, pp_record) (*Define the state type*)
    pp_end_package machine  (*End the package*)

end
