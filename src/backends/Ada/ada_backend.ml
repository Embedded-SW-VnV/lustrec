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

let indent_size = 2

(** Log at level 2 a string message with some indentation.
   @param indent the indentation level
   @param info the message
**)
let log_str_level_two indent info =
  let str_indent = String.make (indent*indent_size) ' ' in
  let pp_message fmt = fprintf fmt "%s.. %s@." str_indent info in
  Log.report ~level:2 pp_message

(** Encapsulate a pretty print function to lower case its result when applied
   @param pp the pretty print function
   @param fmt the formatter
   @param arg the argument of the pp function
**)
let pp_lowercase pp fmt arg =
  let str = asprintf "%a" pp arg in
  fprintf fmt "%s" (String. lowercase_ascii str)

(** Write a new file with formatter
   @param destname folder where the file shoudl be created
   @param pp_filename function printing the filename
   @param pp_file function wich pretty print the file
   @param arg will be given to pp_filename and pp_file
**)
let write_file destname pp_filename pp_file arg =
  let path = asprintf "%s%a" destname pp_filename arg in
  let out = open_out path in
  let fmt = formatter_of_out_channel out in
  pp_file fmt arg;
  pp_print_flush fmt ();
  close_out out;
  log_str_level_two 2 (path^" generated")


(** Print the filename of a package by lowercasing it and appending
  an extension.
   @param extension the extension to append to the package name
   @param fmt the formatter
   @param fmt the machine corresponding to the package
**)
let pp_machine_filename extension fmt machine =
  fprintf fmt "%a.%s"
    (pp_lowercase pp_package_name) machine.mname
    extension

(** Exception raised when a machine contains a feature not supported by the
  Ada backend*)
exception CheckFailed of string


(** Check that a machine match the requirement for an Ada compilation :
      - No constants.
   @param machine the machine to test
**)
let check machine =
  match machine.mconst with
    | [] -> ()
    | _ -> raise (CheckFailed "machine.mconst should be void")

(** Print the name of the ada project file.
   @param fmt the formater to print on
   @param main_machine the machine associated to the main node
**)
let pp_project_name fmt main_machine =
  fprintf fmt "%a.gpr" pp_package_name main_machine.mname

(** Main function of the Ada backend. It calls all the subfunction creating all
the file and fill them with Ada code representing the machines list given.
   @param basename useless
   @param prog useless
   @param prog list of machines to translate
   @param dependencies useless
**)
let translate_to_ada basename prog machines dependencies =
  let module Ads = Ada_backend_ads.Main in
  let module Adb = Ada_backend_adb.Main in
  let module Wrapper = Ada_backend_wrapper.Main in

  (* Extract the main machine if there is one *)
  let main_machine = (match !Options.main_node with
  | "" -> None
  | main_node -> (
    match Machine_code_common.get_machine_opt main_node machines with
    | None -> begin
      Format.eprintf "Ada Code generation error: %a@." Error.pp_error_msg Error.Main_not_found;
      raise (Corelang.Error (Location.dummy_loc, Error.Main_not_found))
    end
    | Some m -> Some m
  )) in

  let destname = !Options.dest_dir ^ "/" in

  log_str_level_two 1 "Checking machines";
  List.iter check machines;

  log_str_level_two 1 "Generating ads";
  List.iter (write_file destname (pp_machine_filename "ads") Ads.pp_file) machines;

  log_str_level_two 1 "Generating adb";
  List.iter (write_file destname (pp_machine_filename "adb") Adb.pp_file) machines;

  (* If a main node is given we generate a main adb file and a project file *)
  log_str_level_two 1 "Generating wrapper files";
  match main_machine with
    | None -> log_str_level_two 2 "File not generated(no -node argument)";
    | Some machine -> begin
        write_file destname pp_project_name Wrapper.pp_project_file machine;
        write_file destname pp_main_filename Wrapper.pp_main_file machine;
      end


(* Local Variables: *)
(* compile-command:"make -C ../../.." *)
(* End: *)