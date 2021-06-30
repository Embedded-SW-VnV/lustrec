(********************************************************************)
(*                                                                  *)
(*  The LustreC compiler toolset   /  The LustreC Development Team  *)
(*  Copyright 2012 -    --   ONERA - CNRS - INPT                    *)
(*                                                                  *)
(*  LustreC is free software, distributed WITHOUT ANY WARRANTY      *)
(*  under the terms of the GNU Lesser General Public License        *)
(*  version 2.1.                                                    *)
(*                                                                  *)
(********************************************************************)

open Utils.Format
open C_backend_mauve

(******************************************************************************)
(*                        Translation function                                *)
(******************************************************************************)
(* USELESS let makefile_opt print basename dependencies makefile_fmt machines =
   (* If a main node is identified, generate a main target for it *) match
   !Options.main_node with | "" -> () | main_node -> ( match
   Machine_code.get_machine_opt main_node machines with | None -> Format.eprintf
   "Unable to find a main node named %s@.@?" main_node; () | Some _ -> print
   basename !Options.main_node dependencies makefile_fmt ) *)

let c_or_cpp f = if !Options.cpp then f ^ ".cpp" else f ^ ".c"
(* Could be changed *)

let with_main_node machines node f =
  if node <> "" then
    (* looking for the main node *)
    match Machine_code_common.get_machine_opt machines node with
    | None ->
      let open Error in
      Global.main_node := node;
      Format.eprintf "Code generation error: %a@." pp Main_not_found;
      raise (Error (Location.dummy, Main_not_found))
    | Some m ->
      f m

let gen_files
    ( print_alloc_header,
      print_lib_c,
      print_main_c,
      print_makefile
    (* , print_cmake *) ) basename prog machines dependencies =
  let destname = !Options.dest_dir ^ "/" ^ basename in

  (* Generating H alloc file *)
  let alloc_header_file = destname ^ "_alloc.h" in
  (* Could be changed *)
  with_out_file alloc_header_file (fun header_fmt ->
      print_alloc_header header_fmt basename machines dependencies);

  (* Generating Lib C file *)
  let source_lib_file = c_or_cpp destname in
  with_out_file source_lib_file (fun source_lib_fmt ->
      print_lib_c source_lib_fmt basename prog machines dependencies);

  (* Generating Main C file *)
  let main_node = !Options.main_node in
  with_main_node machines main_node (fun m ->
      let source_main_file = c_or_cpp (destname ^ "_main") in
      with_out_file source_main_file (fun source_main_fmt ->
          print_main_c source_main_fmt m basename prog machines dependencies));

  (* Generating Mauve files *)
  with_main_node machines !Options.mauve (fun m ->
      let source_mauve_file = destname ^ "_mauve.hpp" in
      with_out_file source_mauve_file (fun source_mauve_fmt ->
          (* Header *)
          print_mauve_header source_mauve_fmt basename;
          (* Shell *)
          print_mauve_shell source_mauve_fmt m;
          (* Core *)
          print_mauve_core source_mauve_fmt m;
          (* FSM *)
          print_mauve_fsm source_mauve_fmt m));

  (* Generating Makefile *)
  (* Makefiles: - for the moment two cases 1. Classical Makefile, only when
     provided with a main node May contain additional framac eacsl targets 2.
     Cmake : 2 files - lustrec-basename.cmake describing all variables - the
     main CMakeLists.txt activating the first file - Later option 1 should be
     removed *)
  (* Case 1 *)
  if main_node <> "" then
    let makefile_file = destname ^ ".makefile" in
    (* Could be changed *)
    with_out_file makefile_file (fun makefile_fmt ->
        print_makefile basename main_node dependencies makefile_fmt)

(* (\* Case 2 *\) *)
(* let cmake_file = "lustrec-" ^ basename ^ ".cmake" in *)
(* let cmake_file_full_path = !Options.dest_dir ^ "/" ^ cmake_file in *)
(* let cmake_out = open_out cmake_file_full_path in *)
(* let cmake_fmt = formatter_of_out_channel cmake_out in *)
(* (\* Generating Makefile *\) *)
(* print_cmake basename main_node dependencies makefile_fmt; *)

(* close_out makefile_out *)

let print_c_header basename =
  let open Options in
  let header_m =
    match !spec with
    | SpecNo ->
      C_backend_header.((module EmptyMod : MODIFIERS_HDR))
    | SpecACSL ->
      C_backend_header.((module C_backend_spec.HdrMod : MODIFIERS_HDR))
    | SpecC ->
      assert false
    (* not implemented yet *)
  in
  let module Header = C_backend_header.Main ((val header_m)) in
  let destname = !dest_dir ^ "/" ^ basename in
  (* Generating H file *)
  let lusic = Lusic.read_lusic destname ".lusic" in
  let header_file = destname ^ ".h" in
  with_out_file header_file (fun header_fmt ->
      assert (not lusic.obsolete);
      Header.print_header_from_header header_fmt basename lusic.contents)

let translate_to_c generate_c_header basename prog machines dependencies =
  let header_m, source_m, source_main_m, makefile_m =
    let open Options in
    match !spec with
    | SpecNo ->
      ( C_backend_header.((module EmptyMod : MODIFIERS_HDR)),
        C_backend_src.((module EmptyMod : MODIFIERS_SRC)),
        C_backend_main.((module EmptyMod : MODIFIERS_MAINSRC)),
        C_backend_makefile.((module EmptyMod : MODIFIERS_MKF)) )
    | SpecACSL ->
      let open C_backend_spec in
      ( C_backend_header.((module HdrMod : MODIFIERS_HDR)),
        C_backend_src.((module SrcMod : MODIFIERS_SRC)),
        C_backend_main.((module EmptyMod : MODIFIERS_MAINSRC)),
        C_backend_makefile.((module MakefileMod : MODIFIERS_MKF)) )
    | SpecC ->
      assert false
    (* not implemented yet *)
  in
  let module Header = C_backend_header.Main ((val header_m)) in
  let module Source = C_backend_src.Main ((val source_m)) in
  let module SourceMain = C_backend_main.Main ((val source_main_m)) in
  let module Makefile = C_backend_makefile.Main ((val makefile_m)) in
  (* let module CMakefile = C_backend_cmake.Main (MakefileMod) in *)
  let funs =
    ( Header.print_alloc_header,
      Source.print_lib_c,
      SourceMain.print_main_c,
      Makefile.print_makefile )
    (* CMakefile.print_makefile *)
  in
  if generate_c_header then print_c_header basename;
  gen_files funs basename prog machines dependencies

(* Local Variables: *)
(* compile-command:"make -C ../../.." *)
(* End: *)
