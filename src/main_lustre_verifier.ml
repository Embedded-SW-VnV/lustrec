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

open Format
open Log
open Compiler_common

open Utils
open Lustre_types
 

let usage = "Usage: lustrev [options] \x1b[4msource file\x1b[0m"

let extensions = [".ec"; ".lus"; ".lusi"]


(* verify a .lus source file 

we have multiple "backends"
- zustre: linked to z3/spacer. Shall preserve the structure and rely on contracts. Produces both a lustre model with new properties, maybe as a lusi with lustre contract, and a JSON summarizing the results and providing tests cases or counter examples if any

- seal: linked to seal. Require global inline and main node
  focuses only on the selected node (the main)
  map the machine code into SEAL datastructure and compute invariants
  - provides the node and its information (typical point of interest for taylor expansion, range for inputs, existing invariants, computation error for the node content)
  - simplification of program through taylor expansion
  - scaling when provided with typical ranges (not required to be sound for the moment)
  - computation of lyapunov invariants
  - returns an annotated node with invariants and a JSON to explain computation
  - could also returns plots

- tiny: linked to tiny library to perform floating point analyses
  shall be provided with ranges for inputs or local variables (memories)
  
*)
let rec verify dirname basename extension =
  let source_name = dirname ^ "/" ^ basename ^ extension in
  Options.compile_header := false; (* to avoid producing .h / .lusic *)
  Log.report ~level:1 (fun fmt -> fprintf fmt "@[<v 0>");
  decr Options.verbose_level;

  (* Parsing source *)
  let prog = parse source_name extension in

  (* Checking which solver is active *)
  incr Options.verbose_level;
  let verifier = Verifiers.get_active () in
  let module Verifier = (val verifier : VerifierType.S) in

  decr Options.verbose_level;
  let params = Verifier.get_normalization_params () in
  (* Normalizing it *)
  let prog, dependencies = 
    Log.report ~level:1 (fun fmt -> fprintf fmt "@[<v 2>.. Phase 1 : Normalisation@,");
    try
      incr Options.verbose_level;
      decr Options.verbose_level;
      Compiler_stages.stage1 params prog dirname basename extension
    with Compiler_stages.StopPhase1 prog -> (
      if !Options.print_nodes then (
        Format.printf "%a@.@?" Printers.pp_node_list prog;
        exit 0
      )
      else
        assert false
    )
  in
  Log.report ~level:1 (fun fmt -> fprintf fmt "@]@,");
  Log.report ~level:3 (fun fmt -> fprintf fmt ".. Normalized program:@ %a@ "Printers.pp_prog prog);

  Log.report ~level:1 (fun fmt -> fprintf fmt "@[<v 2>.. Phase 2 : Machines generation@,");

  let prog, machine_code = 
    Compiler_stages.stage2 params prog 
  in

  Log.report ~level:1 (fun fmt -> fprintf fmt "@]@ ");
  Log.report ~level:3 (fun fmt -> fprintf fmt ".. Generated machines:@ %a@ "
                                    Machine_code_common.pp_machines machine_code);
  
  if Scopes.Plugin.show_scopes () then
    begin
      let all_scopes = Scopes.compute_scopes prog !Options.main_node in
      (* Printing scopes *)
      if !Options.verbose_level >= 1 then
	Format.printf "Possible scopes are:@   ";
      Format.printf "@[<v>%a@ @]@ @?" Scopes.print_scopes all_scopes;
      exit 0
	
    end;

  let machine_code = Plugins.refine_machine_code prog machine_code in

  (*assert (dependencies = []); (* Do not handle deps yet *)*)
  incr Options.verbose_level;
  Verifier.run basename prog machine_code;
  begin
    decr Options.verbose_level;
    Log.report ~level:1 (fun fmt -> fprintf fmt ".. done !@ ");
    incr Options.verbose_level;
    Log.report ~level:1 (fun fmt -> fprintf fmt "@]@.");
    (* We stop the process here *)
    exit 0
  end


let anonymous filename =
  let ok_ext, ext = List.fold_left
    (fun (ok, ext) ext' ->
      if not ok && Filename.check_suffix filename ext' then
	true, ext'
      else
	ok, ext)
    (false, "") extensions in
  if ok_ext then
    let dirname = Filename.dirname filename in
    let basename = Filename.chop_suffix (Filename.basename filename) ext in
    verify dirname basename ext
  else
    raise (Arg.Bad ("Can only compile *.lusi, *.lus or *.ec files"))

let _ =
  Global.initialize ();
  Corelang.add_internal_funs ();
  try
    Printexc.record_backtrace true;

    let options = Options_management.lustrev_options @ (Verifiers.options ()) in
    
    Arg.parse options anonymous usage
  with
  | Parse.Error _
    | Types.Error (_,_) | Clocks.Error (_,_) -> exit 1
  | Error.Error (loc , kind) (*| Task_set.Error _*) -> 
     Error.pp_error loc (fun fmt -> Error.pp_error_msg fmt kind);
     exit (Error.return_code kind)
  (* | Causality.Error _  -> exit (Error.return_code Error.AlgebraicLoop) *)
  | Sys_error msg -> (eprintf "Failure: %s@." msg); exit 1
  | exc -> (track_exception (); raise exc) 

             (* Local Variables: *)
             (* compile-command:"make -C .." *)
             (* End: *)
