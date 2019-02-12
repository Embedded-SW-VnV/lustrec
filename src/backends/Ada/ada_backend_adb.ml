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

module Main =
struct

(*TODO: Copied from ./ada_backend_ads.ml *)
let pp_package_name fmt machine =
  fprintf fmt "%s" machine.mname.node_id
let pp_begin_package fmt machine =
  fprintf fmt "package body %a is" pp_package_name machine
let pp_end_package fmt machine =
  fprintf fmt "end %a;" pp_package_name machine

let pp_machine_instr machine fmt instr =
    fprintf fmt "instruction"

let print fmt machine =
  let pp_instr = pp_machine_instr machine in
  fprintf fmt "@[<v 2>%a@,%a@]@,%a@."
    pp_begin_package machine
    (Utils.fprintf_list ~sep:"@," pp_instr) machine.mstep.step_instrs
    pp_end_package machine

end
