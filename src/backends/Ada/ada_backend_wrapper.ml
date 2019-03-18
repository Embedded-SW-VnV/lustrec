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
open Lustre_types

module Main =
struct

  (** Print the main procedure
     @param fmt the formater to print on
     @param machine the main machine
     @param locals list of local variable printers
     @param instrs list of instructions printer
  **)
  let pp_main_procedure_definition machine fmt (locals, instrs) =
      pp_procedure_definition
        pp_main_procedure_name
        (pp_simple_prototype pp_main_procedure_name)
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
  let pp_main_adb fmt machine =
    let pp_str str fmt = fprintf fmt "%s"str in
    (* Dependances *)
    let text_io = "Ada.Text_IO" in
    let float_io = "package Float_IO is new Ada.Text_IO.Float_IO(Float)" in
    let integer_io = "package Integer_IO is new Ada.Text_IO.Integer_IO(Integer)" in
    
    (* Locals *)
    let stateVar = "state" in
    let step_parameters = machine.mstep.step_inputs@machine.mstep.step_outputs in
    let pp_local_state_var_decl fmt = pp_node_state_decl [] stateVar fmt machine in
    let apply_pp_var_decl var fmt = pp_machine_var_decl NoMode fmt var in
    let locals = List.map apply_pp_var_decl step_parameters in
    let locals = (pp_str integer_io)::(pp_str float_io)::pp_local_state_var_decl::locals in

    (* Node instructions *)
    let pp_reset fmt =
      fprintf fmt "%a.reset(%s)"
        pp_package_name machine
        stateVar in
    let pp_step fmt =
      fprintf fmt "%a.step(@[%s,@ %a@])"
        pp_package_name machine
        stateVar
        (Utils.fprintf_list ~sep:",@ " pp_var_name) step_parameters in

    (* Stream instructions *)
    let get_basic var = match (Types.repr var.var_type ).Types.tdesc with
        Types.Tbasic x -> x | _ -> assert false in
    let pp_read fmt var =
      match get_basic var with
        | Types.Basic.Tbool ->
            fprintf fmt "%a := Integer'Value(Ada.Text_IO.Get_Line) /= 0"
              pp_var_name var
        | _ ->
            fprintf fmt "%a := %a'Value(Ada.Text_IO.Get_Line)"
              pp_var_name var
              pp_var_type var
    in
    let pp_write fmt var =
      match get_basic var with
        | Types.Basic.Tbool ->
            fprintf fmt "Ada.Text_IO.Put_Line(\"'%a': '\" & (if %a then \"1\" else \"0\") & \"' \")"
              pp_var_name var
              pp_var_name var
        | Types.Basic.Tint ->
            fprintf fmt "Ada.Text_IO.Put(\"'%a': '\");@,Integer_IO.Put(%a);@,Ada.Text_IO.Put_Line(\"' \")"
              pp_var_name var
              pp_var_name var
        | Types.Basic.Treal ->
            fprintf fmt "Ada.Text_IO.Put(\"'%a': '\");@,Float_IO.Put(%a, Fore=>0, Aft=> 15, Exp => 0);@,Ada.Text_IO.Put_Line(\"' \")"
              pp_var_name var
              pp_var_name var
        | Types.Basic.Tstring | Types.Basic.Trat -> assert false (* Could not be the top level inputs *)
    in

    (* Loop instructions *)
    let pp_loop fmt =
      fprintf fmt "while not Ada.Text_IO.End_Of_File loop@,  @[<v>%a;@,%t;@,%a;@]@,end loop"
        (Utils.fprintf_list ~sep:";@," pp_read) machine.mstep.step_inputs
        pp_step
        (Utils.fprintf_list ~sep:";@," pp_write) machine.mstep.step_outputs in
    
    (* Print the file *)
    let instrs = [ pp_reset;
                   pp_loop] in
    fprintf fmt "@[<v>%a;@,%a;@,@,%a;@]"
      pp_private_with (pp_str text_io)
      pp_with_machine machine
      (pp_main_procedure_definition machine) (locals, instrs)

  (** Print the gpr project file.
     @param fmt the formater to print on
     @param machine the main machine
  **)
  let pp_project_file fmt machine =
      fprintf fmt "project %a is@.  for Main use (\"%a\");@.end %a;"
        pp_package_name machine
        (pp_filename "adb") pp_main_procedure_name
        pp_package_name machine

  end
