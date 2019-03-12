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

open Utils
open Format 
open Lustre_types
open Corelang

let check_main () =
  if !Options.main_node = "" then
    begin
      eprintf "Code generation error: %a@." Error.pp_error_msg Error.No_main_specified;
      raise (Error (Location.dummy_loc, Error.No_main_specified))
    end

let create_dest_dir () =
  begin
    if not (Sys.file_exists !Options.dest_dir) then
      begin
	Log.report ~level:1 (fun fmt -> fprintf fmt ".. creating destination directory@ ");
	Unix.mkdir !Options.dest_dir (Unix.stat ".").Unix.st_perm
      end;
    if (Unix.stat !Options.dest_dir).Unix.st_kind <> Unix.S_DIR then
      begin
	eprintf "Failure: destination %s is not a directory.@.@." !Options.dest_dir;
	exit 1
      end
  end

(* Loading Lus/Lusi file and filling type tables with parsed
   functions/nodes *)
let parse filename extension =
  Location.set_input filename;
  let f_in = open_in filename in
  let lexbuf = Lexing.from_channel f_in in
  Location.init lexbuf filename;
  (* Parsing *)
  let prog = 
    try
      match extension with
        ".lusi" ->
        Log.report ~level:1
          (fun fmt -> fprintf fmt ".. parsing header file %s@ " filename);
        Parse.header Parser_lustre.header Lexer_lustre.token lexbuf 
      | ".lus" ->
         Log.report ~level:1 
           (fun fmt -> fprintf fmt ".. parsing source file %s@ " filename);
         Parse.prog Parser_lustre.prog Lexer_lustre.token lexbuf
      | _ -> assert false
    with
    | (Parse.Error err) as exc -> 
       Parse.report_error err;
       raise exc
    | Corelang.Error (loc, err) as exc -> (
      eprintf "Parsing error: %a%a@."
        Error.pp_error_msg err
        Location.pp_loc loc;
      raise exc
    )
  in
  close_in f_in;
  prog
    

let expand_automata decls =
  Log.report ~level:1 (fun fmt -> fprintf fmt ".. expanding automata@ ");
  try
    Automata.expand_decls decls
  with (Corelang.Error (loc, err)) as exc ->
    eprintf "Automata error: %a%a@."
      Error.pp_error_msg err
      Location.pp_loc loc;
    raise exc

let check_stateless_decls decls =
  Log.report ~level:1 (fun fmt -> fprintf fmt ".. checking stateless/stateful status@ ");
  try
    Stateless.check_prog decls
  with (Stateless.Error (loc, err)) as exc ->
    eprintf "Stateless status error: %a%a@."
      Stateless.pp_error err
      Location.pp_loc loc;
    raise exc

let force_stateful_decls decls =
  Log.report ~level:1 (fun fmt -> fprintf fmt ".. forcing stateful status@ ");
  try
    Stateless.force_prog decls
  with (Stateless.Error (loc, err)) as exc ->
    eprintf "Stateless status error: %a%a@."
      Stateless.pp_error err
      Location.pp_loc loc;
    raise exc

let type_decls env decls =  
  Log.report ~level:1 (fun fmt -> fprintf fmt ".. typing@ ");
  let new_env = 
    begin
      try
	Typing.type_prog env decls
      with (Types.Error (loc,err)) as exc ->
	eprintf "Typing error: %a%a@."
	  Types.pp_error err
	  Location.pp_loc loc;
	raise exc
    end 
  in
  if !Options.print_types || !Options.verbose_level > 2 then
    Log.report ~level:1 (fun fmt -> fprintf fmt "@[<v 2>  %a@]@ " Corelang.pp_prog_type decls);
  new_env
      
let clock_decls env decls = 
  Log.report ~level:1 (fun fmt -> fprintf fmt ".. clock calculus@ ");
  let new_env =
    begin
      try
	Clock_calculus.clock_prog env decls
      with (Clocks.Error (loc,err)) as exc ->
	eprintf "Clock calculus error: %a%a@." Clocks.pp_error err Location.pp_loc loc;
	raise exc
    end
  in
  if !Options.print_clocks  || !Options.verbose_level > 2 then
    Log.report ~level:1 (fun fmt -> fprintf fmt "@[<v 2>  %a@]@ " Corelang.pp_prog_clock decls);
  new_env

(* Typing/Clocking with an empty env *)
let check_top_decls header =
  let new_tenv = type_decls Basic_library.type_env header in   (* Typing *)
  let new_cenv = clock_decls Basic_library.clock_env header in   (* Clock calculus *)
  header, new_tenv, new_cenv


(*
 List.fold_right
   (fun top_decl (ty_env, ck_env) ->
     match top_decl.top_decl_desc with
     | Node nd          -> (Env.add_value ty_env nd.node_id nd.node_type,
			    Env.add_value ck_env nd.node_id nd.node_clock)
     | ImportedNode ind -> (Env.add_value ty_env ind.nodei_id ind.nodei_type,
			    Env.add_value ck_env ind.nodei_id ind.nodei_clock)
     | Const c          -> get_envs_from_const c (ty_env, ck_env)
     | TypeDef _        -> List.fold_left (fun envs top -> consts_of_enum_type top_decl
     | Open _           -> (ty_env, ck_env))
   header
   (Env.initial, Env.initial)
 *)

	 

    
let check_compatibility (prog, computed_types_env, computed_clocks_env) (header, declared_types_env, declared_clocks_env) =
  try
    (* checking defined types are compatible with declared types*)
    Typing.check_typedef_compat header;

    (* checking type compatibility with computed types*)
    Typing.check_env_compat header declared_types_env computed_types_env;

    (* checking clocks compatibility with computed clocks*)
    Clock_calculus.check_env_compat header declared_clocks_env computed_clocks_env;

    (* checking stateless status compatibility *)
    Stateless.check_compat header
  with
  | (Types.Error (loc,err)) as exc ->
    eprintf "Type mismatch between computed type and declared type in lustre interface file: %a%a@."
      Types.pp_error err
      Location.pp_loc loc;
    raise exc
  | Clocks.Error (loc, err) as exc ->
    eprintf "Clock mismatch between computed clock and declared clock in lustre interface file: %a%a@."
      Clocks.pp_error err
      Location.pp_loc loc;
    raise exc
  | Stateless.Error (loc, err) as exc ->
    eprintf "Stateless status mismatch between defined status and declared status in lustre interface file: %a%a@."
      Stateless.pp_error err
      Location.pp_loc loc;
    raise exc

(* Process each node/imported node and introduce the associated contract node *)
let resolve_contracts prog =
  (* Bind a fresh node with a new name according to existing nodes and freshly binded contract node. Clean the contract to remove the stmts  *)
  let process_contract new_contracts prog c =
    (* Resolve first the imports *)
    let stmts, locals, c =
      List.fold_left (
          fun (stmts, locals, c) import ->
          (* Search for contract in prog.
             The node have to be processed already. Otherwise raise an error.
             Each stmts in injected with a fresh name
             Inputs are renamed and associated to the expression in1
             Same thing for outputs.

             Last the contracts elements are replaced with the renamed vars and merged with c contract.
           *)
          let name = import.import_nodeid in
          assert false; (* TODO: we do not handle imports yet.  The
                           algorithm is sketched below *)
        (*
          try
            let imp_nd = xxx in (* Get the contract node in prog *)
            (* checking that it's actually a (processed) contract *)
            let imp_c =
              match imp_nd.node_spec with
                Some (Contract imp_c) ->
                 if imp_c.imports = [] then
                   imp_c
                 else
                   assert false (* should be processed *)
              | _ -> assert false (* should be a contract *)
            in  
            (* Preparing vars: renaming them *)
            let imp_in = rename imp_nd.node_inputs in
            let imp_out = rename imp_nd.node_outputs in
            let imp_locals = rename imp_nd.node_locals in
            let locals = imp_in@imp_out@imp_locals@locals in
            (* Assinging in and out *)
            let in_assigns =
              xxx imp_in = import.inputs
            in
            let out_assigns =
              xxx imp_out = import.outputs
            in
            let stmts = stmts @ (rename imp_nd.stmts) in
            let imp_c = rename imp_c in
            let c = merge_contracts c imp_c in
            stmts, locals, c 
          with Not_found -> raise (Error.Unbound_symbol ("contract " ^ name))

                            *)
        ) ([], c.consts@c.locals, c) c.imports
    in
    (* Other contract elements will be normalized later *)
    let c = { c with
              locals = [];
              consts = [];
              stmts = [];
              imports = []
            }
    in
    stmts, locals, c
    
  in
  let process_contract_new_node accu_contracts prog top =
    let id, spec, inputs, outputs =
      match top.top_decl_desc with
      | Node nd -> nd.node_id, nd.node_spec, nd.node_inputs, nd.node_outputs
      | ImportedNode ind -> ind.nodei_id, ind.nodei_spec, ind.nodei_inputs, ind.nodei_outputs
      | _ -> assert false
    in
    let stmts, locals, c =
      match spec with
      | None | Some (NodeSpec _) -> assert false
      | Some (Contract c) ->
         process_contract accu_contracts prog c
    in
    (* Create a fresh name *)
    let used v = List.exists (fun top ->
                     match top.top_decl_desc with
                     | Node _
                       | ImportedNode _ ->
                        (node_name top) = v
                     | _ -> false
                   ) (accu_contracts@prog)
    in
    let new_nd_id = mk_new_name used (id ^ "_coco") in
    let new_nd =
      mktop_decl
        c.spec_loc
        top.top_decl_owner
        top.top_decl_itf
      (Node {
           node_id = new_nd_id;
	   node_type = Types.new_var ();
	   node_clock = Clocks.new_var true;
	   node_inputs = inputs;
	   node_outputs = outputs;
	   node_locals = locals;
	   node_gencalls = [];
	   node_checks = [];
	   node_asserts = []; 
	   node_stmts = stmts;
	   node_dec_stateless = false;
	   node_stateless = None;
	   node_spec = Some (Contract c);
	   node_annot = [];
	   node_iscontract = true;
      }) in
    new_nd
  in
  (* Processing nodes in order. Should have been sorted by now

     Each top level contract is processed: stmts pushed in node

     Each regular imported node or node associated with a contract is
     replaced with a simplidfied contract and its contract is bound to
     a fresh node.

   *)
  let new_contracts, prog =
    List.fold_left
      (
        fun (accu_contracts, accu_nodes) top ->
        match top.top_decl_desc with
          
        | Node nd when nd.node_iscontract -> (
          match nd.node_spec with
          | None | Some (NodeSpec _) -> assert false
          | Some (Contract c) ->
             let stmts, locals, c = process_contract accu_contracts prog c in
             let nd =
               { nd with
                 node_locals = nd.node_locals @ locals;
                 node_stmts = nd.node_stmts @ stmts;
                 node_spec = Some (Contract c);
               }
             in
             { top with top_decl_desc = Node nd }::accu_contracts,
             accu_nodes
             
        )
        | Node nd -> (
          match nd.node_spec with
          | None -> accu_contracts, top::accu_nodes (* A boring node: no contract *)
          | Some (NodeSpec id) -> (* shall not happen, its too early *)
             assert false
          | Some (Contract c) -> (* A contract: processing it *)
             (* we bind a fresh node *)
             let new_nd = process_contract_new_node accu_contracts prog top in
             Format.eprintf "Creating new contract node %s@." (node_name new_nd);
             let nd = { nd with node_spec = (Some (NodeSpec (node_name new_nd))) } in
             new_nd::accu_contracts,
             { top with top_decl_desc = Node nd }::accu_nodes
             
        )
                   
        | ImportedNode ind -> ( (* Similar treatment for imported nodes *)
          match ind.nodei_spec with
            None -> accu_contracts, top::accu_nodes (* A boring node: no contract *)
          | Some (NodeSpec id) -> (* shall not happen, its too early *)
             assert false
          | Some (Contract c) -> (* A contract: processing it *)
             (* we bind a fresh node *)
             let new_nd = process_contract_new_node accu_contracts prog top in
             let ind = { ind with nodei_spec = (Some (NodeSpec (node_name new_nd))) } in
             new_nd::accu_contracts,
             { top with top_decl_desc = ImportedNode ind }::accu_nodes
        )
        | _ -> accu_contracts, top::accu_nodes
      ) ([],[]) prog
  in
  (List.rev new_contracts) @ (List.rev prog)
         

  
let track_exception () =
  if !Options.track_exceptions
  then (Printexc.print_backtrace stdout; flush stdout)
  else ()


let update_vdecl_parents_prog prog =
  let update_vdecl_parents parent v =
    v.var_parent_nodeid <- Some parent
  in
  List.iter (
    fun top -> match top.top_decl_desc with
    | Node nd ->
       List.iter
	 (update_vdecl_parents nd.node_id)
	 (nd.node_inputs @ nd.node_outputs @ nd.node_locals )  
    | ImportedNode ind -> 
       List.iter
	 (update_vdecl_parents ind.nodei_id)
	 (ind.nodei_inputs @ ind.nodei_outputs )  
    | _ -> ()
  ) prog
