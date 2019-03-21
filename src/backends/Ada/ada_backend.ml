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
  Log.report ~level:2 pp_message;
  Format.pp_print_flush Format.err_formatter ()

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
  log_str_level_two 2 ("generating "^path);
  pp_file fmt arg;
  pp_print_flush fmt ();
  close_out out


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


let get_typed_submachines machines m =
  let instances = List.filter (fun (id, _) -> not (is_builtin_fun id)) m.mcalls in
  let submachines = List.map (get_machine machines) instances in
  List.map2
    (fun instance submachine ->
      let ident = (fst instance) in
      ident, (get_substitution m ident submachine, submachine))
    instances submachines

(** Main function of the Ada backend. It calls all the subfunction creating all
the file and fill them with Ada code representing the machines list given.
   @param basename name of the lustre file
   @param prog useless
   @param prog list of machines to translate
   @param dependencies useless
**)
let translate_to_ada basename prog machines dependencies =
  let module Ads = Ada_backend_ads.Main in
  let module Adb = Ada_backend_adb.Main in
  let module Wrapper = Ada_backend_wrapper.Main in

  let typed_submachines =
    List.map (get_typed_submachines machines) machines in

  let _machines = List.combine typed_submachines machines in

  let _pp_filename ext fmt (typed_submachine, machine) =
    pp_machine_filename ext fmt machine in

  (* Extract the main machine if there is one *)
  let main_machine = (match !Options.main_node with
  | "" -> None
  | main_node -> (
    match Machine_code_common.get_machine_opt machines main_node with
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
  List.iter (write_file destname (_pp_filename "ads") Ads.pp_file) _machines;

  log_str_level_two 1 "Generating adb";
  List.iter (write_file destname (_pp_filename "adb") Adb.pp_file) _machines;

  (* If a main node is given we generate a main adb file and a project file *)
  log_str_level_two 1 "Generating wrapper files";
  (match main_machine with
    | None -> ()
    | Some machine ->
        write_file destname pp_main_filename Wrapper.pp_main_adb machine;
        write_file destname (Wrapper.pp_project_name (basename^"_exe")) (Wrapper.pp_project_file machines basename) main_machine);
  write_file destname Wrapper.pp_project_configuration_name Wrapper.pp_project_configuration_file basename;
  write_file destname (Wrapper.pp_project_name (basename^"_lib")) (Wrapper.pp_project_file machines basename) None;


(* Local Variables: *)
(* compile-command:"make -C ../../.." *)
(* End: *)
