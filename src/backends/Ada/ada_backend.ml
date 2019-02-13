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

let gen_ada destname print suffix machine =
  let path = destname ^ machine.mname.node_id ^ suffix in
  let out = open_out path in
  let fmt = formatter_of_out_channel out in
  print fmt machine;
  close_out out;
  Log.report ~level:2 (fun fmt -> fprintf fmt "    .. %s generated @." path)

exception CheckFailed of string

let check machine =
  match machine.mconst with
    | [] -> ()
    | _ -> raise (CheckFailed "machine.mconst should be void")

let translate_to_ada basename prog machines dependencies =
  let module Ads = Ada_backend_ads.Main in
  let module Adb = Ada_backend_adb.Main in
  let module Wrapper = Ada_backend_wrapper.Main in

  let destname = !Options.dest_dir ^ "/" in

  Log.report ~level:2 (fun fmt -> fprintf fmt "  .. Checking machines@.");

  List.iter check machines;

  Log.report ~level:2 (fun fmt -> fprintf fmt "  .. Generating ads@.");

  List.iter (gen_ada destname Ads.print ".ads") machines;

  Log.report ~level:2 (fun fmt -> fprintf fmt "  .. Generating adb@.");

  List.iter (gen_ada destname Adb.print ".adb") machines

(* Local Variables: *)
(* compile-command:"make -C ../../.." *)
(* End: *)
