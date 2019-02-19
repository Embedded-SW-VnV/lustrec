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
open Ada_backend_common

module Main =
struct

(** Print the main procedure
   @param fmt the formater to print on
   @param machine the main machine
   @param locals list of local variable printers
   @param instrs list of instructions printer
**)
let pp_main_procedure_definition machine fmt (locals, instrs) =
    let pp_name = pp_main_procedure_name machine in
    pp_procedure_definition
      pp_name
      (pp_simple_prototype pp_name)
      (fun fmt local -> fprintf fmt "%t" local)
      (fun fmt instr -> fprintf fmt "%t" instr)
      fmt
      (locals, instrs)

(** Print call to machine procedure on state.
   @param instance name of the variable
   @param fmt the formater to print on
   @param instance node
**)
let pp_node_reset_call name fmt node =
  let pp_package fmt = pp_package_name fmt node in
  let pp_type fmt = pp_package_access fmt (pp_package, pp_state_type) in
  let pp_name fmt = pp_clean_ada_identifier fmt name in
  pp_var_decl fmt (NoMode, pp_name, pp_type)

(** Print the main file calling in a loop the step function of the main machine.
   @param fmt the formater to print on
   @param machine the main machine
**)
let pp_main_file fmt machine =
  let stateVar = "state" in
  let step_parameters = machine.mstep.step_inputs@machine.mstep.step_outputs in
  let pp_local_state_var_decl fmt = pp_node_state_decl stateVar fmt machine.mname in
  let apply_pp_var_decl var fmt = pp_machine_var_decl NoMode fmt var in
  let locals = List.map apply_pp_var_decl step_parameters in
  let locals = pp_local_state_var_decl::locals in
  let pp_reset fmt =
    fprintf fmt "%a.reset(%s)"
      pp_package_name machine.mname
      stateVar in
  let pp_loop fmt =
    fprintf fmt "while true loop@,  %a.step(@[%s,@ %a@]);@,end loop"
      pp_package_name machine.mname
      stateVar
      (Utils.fprintf_list ~sep:",@ " pp_var_name) step_parameters
      in
  let instrs = [pp_reset; pp_loop] in
  fprintf fmt "@[<v>%a;@,@,%a;@]"
    pp_with_node machine.mname
    (pp_main_procedure_definition machine) (locals, instrs)

(** Print the gpr project file.
   @param fmt the formater to print on
   @param machine the main machine
**)
let pp_project_file fmt machine =
    fprintf fmt "project %a is@.  for Main use (\"%a\");@.end %a;"
      pp_package_name machine.mname
      pp_main_filename machine
      pp_package_name machine.mname

end
