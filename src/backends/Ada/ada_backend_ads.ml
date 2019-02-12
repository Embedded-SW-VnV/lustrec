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

(** Print the package declaration(ads) of a lustre node.
   @param fmt the formater to print on
   @param machine the machine
*)
let print fmt machine =
  fprintf fmt "@[<v 2>%a;@,%a;@,%a;@,%a;@,%a;@]@,%a@."
    (pp_begin_package false) machine
    pp_init_prototype machine
    pp_step_prototype machine
    pp_reset_prototype machine
    pp_clear_prototype machine
    pp_end_package machine
    (*(Utils.fprintf_list ~sep:"@," pp_var_decl) machine.mmemory*)

end
