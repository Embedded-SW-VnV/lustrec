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
    fprintf fmt "instruction"

let print fmt machine =
  let pp_instr = pp_machine_instr machine in
  fprintf fmt "@[<v 2>%a@,%a@]@,%a@."
    (pp_begin_package true) machine
    (Utils.fprintf_list ~sep:"@," pp_instr) machine.mstep.step_instrs
    pp_end_package machine

end
