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
open Lustre_types
open Corelang

let add_symbol loc msg hashtbl name value =
 if Hashtbl.mem hashtbl name
 then raise (Error (loc, Error.Already_bound_symbol msg))
 else Hashtbl.add hashtbl name value

let check_symbol loc msg hashtbl name =
 if not (Hashtbl.mem hashtbl name)
 then raise (Error (loc, Error.Unbound_symbol msg))
 else ()


let add_imported_node name value =
(*Format.eprintf "add_imported_node %s %a (owner=%s)@." name Printers.pp_imported_node (imported_node_of_top value) value.top_decl_owner;*)
  try
    let value' = Hashtbl.find node_table name in
    let owner' = value'.top_decl_owner in
    let itf' = value'.top_decl_itf in
    let owner = value.top_decl_owner in
    let itf = value.top_decl_itf in
    match value'.top_decl_desc, value.top_decl_desc with
    | Node _        , ImportedNode _  when owner = owner' && itf' && (not itf) -> Hashtbl.add node_table name value
    | ImportedNode _, ImportedNode _            -> raise (Error (value.top_decl_loc, Error.Already_bound_symbol ("node " ^ name)))
    | _                                         -> assert false
  with
    Not_found                                   -> Hashtbl.add node_table name value

let add_node name value =
(*Format.eprintf "add_node %s %a (owner=%s)@." name Printers.pp_imported_node (get_node_interface (node_of_top value)) value.top_decl_owner;*)
  try
    let value' = Hashtbl.find node_table name in
    let owner' = value'.top_decl_owner in
    let itf' = value'.top_decl_itf in
    let owner = value.top_decl_owner in
    let itf = value.top_decl_itf in
    match value'.top_decl_desc, value.top_decl_desc with
    | ImportedNode _, Node _          when owner = owner' && itf' && (not itf) -> ()
    | Node _        , Node _                    -> raise (Error (value.top_decl_loc, Error.Already_bound_symbol ("node " ^ name)))
    | _                                         -> assert false
  with
    Not_found                                   -> Hashtbl.add node_table name value


let add_tag loc name typ =
  if Hashtbl.mem tag_table name then
    raise (Error (loc, Error.Already_bound_symbol ("enum tag " ^ name)))
  else Hashtbl.add tag_table name typ

let add_field loc name typ =
  if Hashtbl.mem field_table name then
    raise (Error (loc, Error.Already_bound_symbol ("struct field " ^ name)))
  else Hashtbl.add field_table name typ

let import_typedef name tydef =
  let loc = tydef.top_decl_loc in
  let rec import ty =
    match ty with
    | Tydec_enum tl   ->
       List.iter (fun tag -> add_tag loc tag tydef) tl
    | Tydec_struct fl -> 
       List.iter (fun (field, ty) -> add_field loc field tydef; import ty) fl
    | Tydec_clock ty      -> import ty
    | Tydec_const c       ->
       if not (Hashtbl.mem type_table (Tydec_const c))
       then raise (Error (loc, Error.Unbound_symbol ("type " ^ c)))
       else ()
    | Tydec_array (c, ty) -> import ty
    | _                   -> ()
  in import ((typedef_of_top tydef).tydef_desc)

let add_type itf name value =
(*Format.eprintf "Modules.add_type %B %s %a (owner=%s)@." itf name Printers.pp_typedef (typedef_of_top value) value.top_decl_owner;*)
  try
    let value' = Hashtbl.find type_table (Tydec_const name) in
    let owner' = value'.top_decl_owner in
    let itf' = value'.top_decl_itf in
    let owner = value.top_decl_owner in
    let itf = value.top_decl_itf in
    match value'.top_decl_desc, value.top_decl_desc with
    | TypeDef ty', TypeDef ty when coretype_equal ty'.tydef_desc ty.tydef_desc && owner' = owner && itf' && (not itf) -> ()
    | TypeDef ty', TypeDef ty -> raise (Error (value.top_decl_loc, Error.Already_bound_symbol ("type " ^ name)))
    | _       -> assert false
  with Not_found -> (import_typedef name value; Hashtbl.add type_table (Tydec_const name) value)

let check_type loc name =
 if not (Hashtbl.mem type_table (Tydec_const name))
 then raise (Error (loc, Error.Unbound_symbol ("type " ^ name)))
 else ()

let add_const itf name value =
  try
    let value' = Hashtbl.find consts_table name in
    let owner' = value'.top_decl_owner in
    let itf' = value'.top_decl_itf in
    let owner = value.top_decl_owner in
    let itf = value.top_decl_itf in
    match value'.top_decl_desc, value.top_decl_desc with
    | Const c', Const c when c.const_value = c'.const_value && owner' = owner && itf' && (not itf) -> ()
    | Const c', Const c -> raise (Error (value.top_decl_loc, Error.Already_bound_symbol ("const " ^ name)))
    | _       -> assert false
  with Not_found -> Hashtbl.add consts_table name value

(* let import_dependency_aux loc (local, dep) =
 *   let basename = Options_management.name_dependency (local, dep) in
 *   let extension = ".lusic" in 
 *   try
 *     let lusic = Lusic.read_lusic basename extension in
 *     Lusic.check_obsolete lusic basename;
 *     lusic
 *   with
 *   | Sys_error msg ->
 *       raise (Error (loc, Error.Unknown_library basename))
 *     
 * let import_dependency loc (local, dep) =
 *   try
 *     import_dependency_aux loc (local, dep)
 *   with
 *   | Corelang.Error (_, err) as exc -> (
 *     Format.eprintf "Import error: %a%a@."
 *       Error.pp_error_msg err
 *       Location.pp_loc loc;
 *     raise exc
 *   ) *)

let get_lusic decl =
  match decl.top_decl_desc with
  | Open (local, dep) -> (
    let loc = decl.top_decl_loc in
    let extension = ".lusic" in 
    let basename = Options_management.name_dependency (local, dep) extension in
    try
      let lusic = Lusic.read_lusic basename extension in
      Lusic.check_obsolete lusic basename;
      lusic
    with
    | Sys_error msg ->
       raise (Error (loc, Error.Unknown_library basename))
  )
  | _ -> assert false (* should not happen *)


let get_envs_from_const const_decl (ty_env, ck_env) =
  (Env.add_value ty_env const_decl.const_id const_decl.const_type,
   Env.add_value ck_env const_decl.const_id (Clocks.new_var true))

let get_envs_from_consts const_decls (ty_env, ck_env) =
  List.fold_right get_envs_from_const const_decls (ty_env, ck_env)

let rec get_envs_from_top_decl (ty_env, ck_env) top_decl =
  match top_decl.top_decl_desc with
  | Node nd          -> (Env.add_value ty_env nd.node_id nd.node_type,
			 Env.add_value ck_env nd.node_id nd.node_clock)
  | ImportedNode ind -> (Env.add_value ty_env ind.nodei_id ind.nodei_type,
			 Env.add_value ck_env ind.nodei_id ind.nodei_clock)
  | Const c          -> get_envs_from_const c (ty_env, ck_env)
  | TypeDef _        -> List.fold_left get_envs_from_top_decl (ty_env, ck_env) (consts_of_enum_type top_decl)
  | Include _ | Open _           -> (ty_env, ck_env)

(* get type and clock environments from a header *)
let get_envs_from_top_decls header =
  List.fold_left get_envs_from_top_decl (Env.initial, Env.initial) header

  let is_stateful topdecl =
  match topdecl.top_decl_desc with
  | Node nd -> (match nd.node_stateless with Some b -> not b | None -> not nd.node_dec_stateless)
  | ImportedNode nd -> not nd.nodei_stateless 
  | _ -> false

let rec load_rec ~is_header accu program =
  List.fold_left (fun ((accu_prog, accu_dep, typ_env, clk_env) as accu) decl ->
      (* Precompute the updated envs, will not be used in the Open case *)
      let typ_env', clk_env' = get_envs_from_top_decl (typ_env, clk_env) decl in
      match decl.top_decl_desc with
      | Open (local, dep) ->
         (* loading the dep *)
         let basename = Options_management.name_dependency (local, dep) ".lusic" in
         if List.exists
              (fun dep -> basename = Options_management.name_dependency (dep.local, dep.name) ".lusic")
              accu_dep
         then
           (* Library already imported. Just skip *)
           accu
         else (
           Log.report ~level:1 (fun fmt -> Format.fprintf fmt "@ .. Library %s@ " basename);
           let lusic = get_lusic decl in
           (* Recursive call with accumulator on lusic *)
           let (accu_prog, accu_dep, typ_env, clk_env) =
             load_rec ~is_header:true accu lusic.Lusic.contents in
           (* Building the dep *)
           let is_stateful = List.exists is_stateful lusic.Lusic.contents in
           let new_dep = { local = local;
                           name = dep;
                           content = lusic.Lusic.contents;
                           is_stateful = is_stateful } in
           
           (* Returning the prog without the Open, the deps with the new
            one and the updated envs *)
           accu_prog, (new_dep::accu_dep), typ_env, clk_env
         )
      | Include name ->
         let basename = Options_management.name_dependency (true, name) "" in
         let include_src = Compiler_common.parse_source basename in
         load_rec ~is_header:false accu include_src
                         

      | Node nd ->
         if is_header then
           raise (Error(decl.top_decl_loc,
                        LoadError ("node " ^ nd.node_id ^ " declared in a header file")))  
         else (
           (* Registering node *)
           add_node nd.node_id decl;
           (* Updating the type/clock env *)
           decl::accu_prog, accu_dep, typ_env', clk_env'                   
         )
        
      | ImportedNode ind ->
         if is_header then (
           add_imported_node ind.nodei_id decl;
           decl::accu_prog, accu_dep, typ_env', clk_env'                   
         )
         else
           raise (Error(decl.top_decl_loc,
                        LoadError ("imported node " ^ ind.nodei_id ^
                                     " declared in a regular Lustre file")))  
      | Const c -> (
        add_const is_header c.const_id decl;
        decl::accu_prog, accu_dep, typ_env', clk_env' 
      )
      | TypeDef tdef -> (
        add_type is_header tdef.tydef_id decl;
        decl::accu_prog, accu_dep, typ_env', clk_env'
      )
    ) accu program

(* Iterates through lusi definitions and records them in the hashtbl. Open instructions are evaluated and update these hashtbl as well. node_table/type/table/consts_table *)
let load ~is_header program =
  
  try
    let prog, deps, typ_env, clk_env =  
      load_rec ~is_header
        ([], (* accumulator for program elements *)
         [], (* accumulator for dependencies *)
         Env.initial, (* empty type env *)
         Env.initial  (* empty clock env *)
        ) program
    in
    List.rev prog, List.rev deps, (typ_env, clk_env)
  with
    Corelang.Error (loc, err) as exc -> (
    Format.eprintf "Import error: %a%a@."
      Error.pp_error_msg err
      Location.pp_loc loc;
    raise exc
  );;
