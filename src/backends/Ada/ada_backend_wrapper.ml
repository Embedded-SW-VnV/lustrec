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

open Misc_printer
open Misc_lustre_function
open Ada_printer
open Ada_backend_common

module Main =
struct

  let build_text_io_package_local typ =
    AdaLocalPackage (
      (fun fmt -> fprintf fmt "%s_IO" typ),
      (fun fmt -> fprintf fmt "Ada.Text_IO.%s_IO" typ),
      [((fun fmt -> fprintf fmt "Num"), (fun fmt -> fprintf fmt "%s" typ))])

  (** Print the main file calling in a loop the step function of the main machine.
     @param fmt the formater to print on
     @param machine the main machine
  **)
  let pp_main_adb typed_submachines fmt machine =
    let statefull = is_machine_statefull machine in
    
    let pp_package = pp_package_name_with_polymorphic [] machine in
    
    (* Dependances *)
    let text_io = "Ada.Text_IO" in
    
    (* Locals *)
    let locals =
      [[build_text_io_package_local "Integer";build_text_io_package_local "Float"]]
      @(if statefull then [[AdaLocalVar (build_pp_state_decl_from_subinstance (asprintf "%t" pp_state_name, ([], machine)))]] else [])
      @(if machine.mstep.step_inputs != [] then [List.map build_pp_var_decl_local machine.mstep.step_inputs] else [])
      @(if machine.mstep.step_outputs != [] then [List.map build_pp_var_decl_local machine.mstep.step_outputs] else [])
    in

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
      let args = pp_state_name::(List.map (fun x fmt -> pp_var_name fmt x) (machine.mstep.step_inputs@machine.mstep.step_outputs)) in
      fprintf fmt "while not Ada.Text_IO.End_Of_File loop@,  @[<v>%a;@,%a;@,%a;@]@,end loop"
        (Utils.fprintf_list ~sep:";@," pp_read) machine.mstep.step_inputs
        pp_call (pp_package_access (pp_package, pp_step_procedure_name), [args])
        (Utils.fprintf_list ~sep:";@," pp_write) machine.mstep.step_outputs in
    
    (* Print the file *)
    let instrs = (if statefull then [fun fmt -> pp_call fmt (pp_package_access (pp_package, pp_reset_procedure_name), [[pp_state_name]])] else [])@[pp_loop] in
    fprintf fmt "@[<v>%a;@,%a;@,@,%a;@]"
      (pp_with AdaPrivate) (pp_str text_io)
      (pp_with AdaPrivate) (pp_package_name machine)
      (pp_procedure pp_main_procedure_name [] None) (AdaProcedureContent (locals, instrs))

  (** Print the name of the ada project configuration file.
     @param fmt the formater to print on
     @param main_machine the machine associated to the main node
  **)
  let pp_project_configuration_name fmt basename =
    fprintf fmt "%s.adc" basename

  (** Print the project configuration file.
     @param fmt the formater to print on
     @param machine the main machine
  **)
  let pp_project_configuration_file fmt machine =
    fprintf fmt "pragma SPARK_Mode (On);"

  (** Print the name of the ada project file.
     @param base_name name of the lustre file
     @param fmt the formater to print on
     @param machine_opt the main machine option
  **)
  let pp_project_name basename fmt machine_opt =
    fprintf fmt "%s.gpr" basename

  let pp_for_single name arg fmt =
    fprintf fmt "for %s use \"%s\"" name arg

  let pp_for name args fmt =
    fprintf fmt "for %s use (@[%a@])" name
      (Utils.fprintf_list ~sep:",@ " (fun fmt arg -> fprintf fmt "\"%s\"" arg))
      args

  let pp_content fmt lines =
    fprintf fmt "  @[<v>%a%t@]"
      (Utils.fprintf_list ~sep:";@," (fun fmt pp -> fprintf fmt "%t" pp)) lines
      (Utils.pp_final_char_if_non_empty ";" lines)

  let pp_package name lines fmt =
    fprintf fmt "package %s is@,%a@,end %s"
      name
      pp_content lines
      name

  (** Print the gpr project file, if there is a machine in machine_opt then
        an executable project is made else it is a library.
     @param fmt the formater to print on
     @param machine_opt the main machine option
  **)
  let pp_project_file machines basename fmt machine_opt =
    let adbs = (List.map (asprintf "%a" (pp_machine_filename "adb")) machines)
                  @(match machine_opt with
                    | None -> []
                    | Some m -> [asprintf "%a" pp_main_filename m]) in
    let project_name = basename^(if machine_opt=None then "_lib" else "_exe") in
    fprintf fmt "%sproject %s is@,%a@,end %s;" (if machine_opt=None then "library " else "") project_name
    pp_content
    ((match machine_opt with
      | None -> [
          pp_for_single "Library_Name" basename;
          pp_for_single "Library_Dir" "lib";
        ]
      | Some machine -> [
          pp_for "Main" [asprintf "%t" pp_main_procedure_name];
          pp_for_single "Exec_Dir" "bin";
        ])
    @[
      pp_for_single "Object_Dir" "obj";
      pp_for "Source_Files" adbs;
      pp_package "Builder" [
        pp_for_single "Global_Configuration_Pragmas" (asprintf "%a" pp_project_configuration_name basename);
      ];
      pp_package "Prove" [
        pp_for "Switches" ["--mode=prove"; "--report=statistics"; "--proof=per_check"; "--warnings=continue"];
      ]
    ])
    project_name


  end
