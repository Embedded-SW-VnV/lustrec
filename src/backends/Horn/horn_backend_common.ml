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
open Lustre_types
open Machine_code_types
open Corelang

let get_machine = Machine_code_common.get_machine

let machine_reset_name id = id ^ "_reset"
let machine_step_name id = id ^ "_step" 
let machine_stateless_name id = id ^ "_fun" 
let pp_machine_reset_name fmt id = fprintf fmt "%s_reset" id
let pp_machine_step_name fmt id = fprintf fmt "%s_step" id
let pp_machine_stateless_name fmt id = fprintf fmt "%s_fun" id

let rec pp_type fmt t =
  if Types.is_bool_type t  then fprintf fmt "Bool" else
  if Types.is_int_type t then fprintf fmt "Int" else 
  if Types.is_real_type t then fprintf fmt "Real" else 
  match (Types.repr t).Types.tdesc with
  | Types.Tconst ty       -> pp_print_string fmt ty
  | Types.Tclock t        -> pp_type fmt t
  | Types.Tarray(dim,ty)   -> fprintf fmt "(Array Int "; pp_type fmt ty; fprintf fmt ")"
  | Types.Tstatic(d, ty)-> pp_type fmt ty
  | Types.Tarrow _
  | _                     -> eprintf "internal error: pp_type %a@."
    Types.print_ty t; assert false

let pp_decl_var fmt id =
  fprintf fmt "(declare-var %s %a)"
    id.var_id
    pp_type id.var_type

(* let pp_var fmt id = pp_print_string fmt id.var_id  *)


let pp_conj pp fmt l =
  match l with
    [] -> assert false
  | [x] -> pp fmt x
  | _ -> fprintf fmt "(and @[<v 0>%a@]@ )" (Utils.fprintf_list ~sep:"@ " pp) l



(********************************************************************************************)
(*                    Workaround to prevent the use of declared keywords as node name       *)
(********************************************************************************************)
let registered_keywords = ["implies"]

let protect_kwd s = 
  if List.mem s registered_keywords then
    "__" ^ s
  else
    s

let node_name n =
  let name = node_name n in
  protect_kwd name


let concat prefix x = if prefix = "" then x else prefix ^ "." ^ x
let rename f = (fun v -> {v with var_id = f v.var_id } )
let rename_machine p = rename (fun n -> concat p n)
let rename_machine_list p = List.map (rename_machine p)

let rename_current =  rename (fun n -> n ^ "_c")
let rename_current_list = List.map rename_current
let rename_mid =  rename (fun n -> n ^ "_m")
let rename_mid_list = List.map rename_mid
let rename_next = rename (fun n -> n ^ "_x")
let rename_next_list = List.map rename_next


let local_memory_vars machines machine =
  rename_machine_list machine.mname.node_id machine.mmemory
    
let instances_memory_vars ?(without_arrow=false) machines machine =
  let rec aux fst prefix m =
    (
      if not fst then (
	(rename_machine_list (concat prefix m.mname.node_id) m.mmemory)
      )
      else []
    ) @
      List.fold_left (fun accu (id, (n, _)) ->
	let name = node_name n in
	if without_arrow && name = "_arrow" then
	  accu 
	else
	  let machine_n = get_machine machines name in
	  ( aux false (concat prefix 
			 (if fst then id else concat m.mname.node_id id))
	      machine_n ) @ accu
      ) [] (m.minstances)
  in
  aux true machine.mname.node_id machine

(* Extract the arrows of a given node/machine *)
let arrow_vars machines machine : Lustre_types.var_decl list =
  let rec aux fst prefix m =
    List.fold_left (fun accu (id, (n, _)) ->
      let name = node_name n in
      if name = "_arrow" then
	let arrow_machine = Machine_code_common.arrow_machine in
	(rename_machine_list
	  (concat prefix (concat (if fst then id else concat m.mname.node_id id) "_arrow"))
	  arrow_machine.mmemory
	) @ accu
      else
	let machine_n = get_machine machines name in
	( aux false (concat prefix
		       (if fst then id else concat m.mname.node_id id))
	    machine_n ) @ accu
    ) [] (m.minstances)
  in
  aux true machine.mname.node_id machine

let full_memory_vars ?(without_arrow=false) machines machine =
  (local_memory_vars machines machine)
  @ (instances_memory_vars ~without_arrow machines machine)

let inout_vars machines m =
  (rename_machine_list m.mname.node_id m.mstep.step_inputs)
  @ (rename_machine_list m.mname.node_id m.mstep.step_outputs)

let step_vars machines m =
  (inout_vars machines m)
  @ (rename_current_list (full_memory_vars machines m)) 
  @ (rename_next_list (full_memory_vars machines m))

let step_vars_m_x machines m =
  (inout_vars machines m)
  @ (rename_mid_list (full_memory_vars machines m)) 
  @ (rename_next_list (full_memory_vars machines m))

let reset_vars machines m =
  (rename_current_list (full_memory_vars machines m)) 
  @ (rename_mid_list (full_memory_vars machines m))

let step_vars_c_m_x machines m =
  (inout_vars machines m) 
  @ (rename_current_list (full_memory_vars machines m)) 
  @ (rename_mid_list (full_memory_vars machines m)) 
  @ (rename_next_list (full_memory_vars machines m))


(* Local Variables: *)
(* compile-command:"make -C ../.." *)
(* End: *)
