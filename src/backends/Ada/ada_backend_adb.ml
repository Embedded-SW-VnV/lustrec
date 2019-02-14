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

module Main =
struct

let pp_machine_instr machine fmt instr =
    fprintf fmt "NULL"

(** Keep only the MReset from an instruction list.
  @param list to filter
**)
let filter_reset instr_list = List.map
  (fun i -> match get_instr_desc i with MReset i -> i | _ -> assert false)
  instr_list

(** Print the definition of the init procedure from a machine.
   @param fmt the formater to print on
   @param machine the machine
**)
let pp_init_definition fmt m = pp_procedure_definition
      pp_init_procedure_name
      (pp_init_prototype m)
      (pp_machine_var_decl NoMode)
      (pp_machine_instr m)
      fmt
      ([], m.minit)

(** Print the definition of the step procedure from a machine.
   @param fmt the formater to print on
   @param machine the machine
**)
let pp_step_definition fmt m = pp_procedure_definition
      pp_step_procedure_name
      (pp_step_prototype m)
      (pp_machine_var_decl NoMode)
      (pp_machine_instr m)
      fmt
      (m.mstep.step_locals, m.mstep.step_instrs)

(** Print the definition of the reset procedure from a machine.
   @param fmt the formater to print on
   @param machine the machine
**)
let pp_reset_definition fmt m = pp_procedure_definition
      pp_reset_procedure_name
      (pp_reset_prototype m)
      (pp_machine_var_decl NoMode)
      (pp_machine_instr m)
      fmt
      ([], m.minit)

(** Print the definition of the clear procedure from a machine.
   @param fmt the formater to print on
   @param machine the machine
**)
let pp_clear_definition fmt m = pp_procedure_definition
      pp_clear_procedure_name
      (pp_clear_prototype m)
      (pp_machine_var_decl NoMode)
      (pp_machine_instr m)
      fmt
      ([], filter_reset m.minit)

(** Print the package definition(adb) of a machine.
   @param fmt the formater to print on
   @param machine the machine
**)
let pp_file fmt machine =
  fprintf fmt "%a@,  @[<v>@,%a;@,@,%a;@,@,%a;@,@,%a;@,@]@,%a;@."
    (pp_begin_package true) machine (*Begin the package*)
    pp_init_definition machine (*Define the init procedure*)
    pp_step_definition machine (*Define the step procedure*)
    pp_reset_definition machine (*Define the reset procedure*)
    pp_clear_definition machine (*Define the clear procedure*)
    pp_end_package machine  (*End the package*)

end
