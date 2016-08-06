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

open LustreSpec
open Corelang
open Utils

(* Local annotations are declared with the following key /inlining/: true *)
let keyword = ["inlining"]

let is_inline_expr expr = 
match expr.expr_annot with
| Some ann -> 
  List.exists (fun (key, value) -> key = keyword) ann.annots
| None -> false

let check_node_name id = (fun t -> 
  match t.top_decl_desc with 
  | Node nd -> nd.node_id = id 
  | _ -> false) 

let is_node_var node v =
 try
   ignore (Corelang.get_node_var v node); true
 with Not_found -> false

let rename_expr rename expr = expr_replace_var rename expr

let rename_eq rename eq = 
  { eq with
    eq_lhs = List.map rename eq.eq_lhs; 
    eq_rhs = rename_expr rename eq.eq_rhs
  }
(*
let get_static_inputs input_arg_list =
 List.fold_right (fun (vdecl, arg) res ->
   if vdecl.var_dec_const
   then (vdecl.var_id, Corelang.dimension_of_expr arg) :: res
   else res)
   input_arg_list []

let get_carrier_inputs input_arg_list =
 List.fold_right (fun (vdecl, arg) res ->
   if Corelang.is_clock_dec_type vdecl.var_dec_type.ty_dec_desc
   then (vdecl.var_id, ident_of_expr arg) :: res
   else res)
   input_arg_list []
*)
(* 
    expr, locals', eqs = inline_call id args' reset locals node nodes

We select the called node equations and variables.
   renamed_inputs = args
   renamed_eqs

the resulting expression is tuple_of_renamed_outputs
   
TODO: convert the specification/annotation/assert and inject them
DONE: annotations
TODO: deal with reset
*)
let inline_call node orig_expr args reset locals caller =
  let loc = orig_expr.expr_loc in
  let uid = orig_expr.expr_tag in
  let rename v =
    if v = tag_true || v = tag_false || not (is_node_var node v) then v else
      Corelang.mk_new_node_name caller (Format.sprintf "%s_%i_%s" node.node_id uid v)
  in
  let eqs' = List.map (rename_eq rename) (get_node_eqs node) in
  let input_arg_list = List.combine node.node_inputs (Corelang.expr_list_of_expr args) in
  let static_inputs, dynamic_inputs = List.partition (fun (vdecl, arg) -> vdecl.var_dec_const) input_arg_list in
  let static_inputs = List.map (fun (vdecl, arg) -> vdecl, Corelang.dimension_of_expr arg) static_inputs in
  let carrier_inputs, other_inputs = List.partition (fun (vdecl, arg) -> Corelang.is_clock_dec_type vdecl.var_dec_type.ty_dec_desc) dynamic_inputs in
  let carrier_inputs = List.map (fun (vdecl, arg) -> vdecl, Corelang.ident_of_expr arg) carrier_inputs in
  let rename_static v =
    try
      snd (List.find (fun (vdecl, _) -> v = vdecl.var_id) static_inputs)
    with Not_found -> Dimension.mkdim_ident loc v in
  let rename_carrier v =
    try
      snd (List.find (fun (vdecl, _) -> v = vdecl.var_id) carrier_inputs)
    with Not_found -> v in
  let rename_var v =
    let vdecl =
      Corelang.mkvar_decl v.var_loc
	(rename v.var_id,
	 { v.var_dec_type  with ty_dec_desc = Corelang.rename_static rename_static v.var_dec_type.ty_dec_desc },
	 { v.var_dec_clock with ck_dec_desc = Corelang.rename_carrier rename_carrier v.var_dec_clock.ck_dec_desc },
	 v.var_dec_const,
	 Utils.option_map (rename_expr rename) v.var_dec_value) in
    begin
(*
      (try
	 Format.eprintf "Inliner.inline_call unify %a %a@." Types.print_ty vdecl.var_type Dimension.pp_dimension (List.assoc v.var_id static_inputs);
	 Typing.unify vdecl.var_type (Type_predef.type_static (List.assoc v.var_id static_inputs) (Types.new_var ()))
       with Not_found -> ());
      (try
Clock_calculus.unify vdecl.var_clock (Clock_predef.ck_carrier (List.assoc v.var_id carrier_inputs) (Clocks.new_var true))
       with Not_found -> ());
(*Format.eprintf "Inliner.inline_call res=%a@." Printers.pp_var vdecl;*)
*)
      vdecl
    end
    (*Format.eprintf "Inliner.rename_var %a@." Printers.pp_var v;*)
  in
  let inputs' = List.map (fun (vdecl, _) -> rename_var vdecl) dynamic_inputs in
  let outputs' = List.map rename_var node.node_outputs in
  let locals' =
      (List.map (fun (vdecl, arg) -> let vdecl' = rename_var vdecl in { vdecl' with var_dec_value = Some (Corelang.expr_of_dimension arg) }) static_inputs)
    @ (List.map rename_var node.node_locals) 
in
  (* checking we are at the appropriate (early) step: node_checks and
     node_gencalls should be empty (not yet assigned) *)
  assert (node.node_checks = []);
  assert (node.node_gencalls = []);

  (* Bug included: todo deal with reset *)
  assert (reset = None);

  let assign_inputs = mkeq loc (List.map (fun v -> v.var_id) inputs', expr_of_expr_list args.expr_loc (List.map snd dynamic_inputs)) in
  let expr = expr_of_expr_list loc (List.map expr_of_vdecl outputs')
  in
  let asserts' = (* We rename variables in assert expressions *)
    List.map 
      (fun a -> 
	{a with assert_expr = 
	    let expr = a.assert_expr in
	    rename_expr rename expr
      })
      node.node_asserts 
  in
  let annots' =
    Plugins.inline_annots rename node.node_annot
  in
  expr, 
  inputs'@outputs'@locals'@locals, 
  assign_inputs::eqs',
  asserts',
  annots'



let inline_table = Hashtbl.create 23

(* 
   new_expr, new_locals, new_eqs = inline_expr expr locals node nodes
   
   Each occurence of a node in nodes in the expr should be replaced by fresh
   variables and the code of called node instance added to new_eqs

*)
let rec inline_expr ?(selection_on_annotation=false) expr locals node nodes =
  let inline_expr = inline_expr ~selection_on_annotation:selection_on_annotation in
  let inline_node = inline_node ~selection_on_annotation:selection_on_annotation in
  let inline_tuple el = 
    List.fold_right (fun e (el_tail, locals, eqs, asserts, annots) -> 
      let e', locals', eqs', asserts', annots' = inline_expr e locals node nodes in
      e'::el_tail, locals', eqs'@eqs, asserts@asserts', annots@annots'
    ) el ([], locals, [], [], [])
  in
  let inline_pair e1 e2 = 
    let el', l', eqs', asserts', annots' = inline_tuple [e1;e2] in
    match el' with
    | [e1'; e2'] -> e1', e2', l', eqs', asserts', annots'
    | _ -> assert false
  in
  let inline_triple e1 e2 e3 = 
    let el', l', eqs', asserts', annots' = inline_tuple [e1;e2;e3] in
    match el' with
    | [e1'; e2'; e3'] -> e1', e2', e3', l', eqs', asserts', annots'
    | _ -> assert false
  in
  
  match expr.expr_desc with
  | Expr_appl (id, args, reset) ->
    let args', locals', eqs', asserts', annots' = inline_expr args locals node nodes in 
    if List.exists (check_node_name id) nodes && (* the current node call is provided
						    as arguments nodes *)
      (not selection_on_annotation || is_inline_expr expr) (* and if selection on annotation is activated, 
							      it is explicitely inlined here *)
    then 
      (* The node should be inlined *)
      (* let _ =     Format.eprintf "Inlining call to %s@." id in *)
      let called = try List.find (check_node_name id) nodes 
	with Not_found -> (assert false) in
      let called = node_of_top called in
      let called' = inline_node called nodes in
      let expr, locals', eqs'', asserts'', annots'' = 
	inline_call called' expr args' reset locals' node in
      expr, locals', eqs'@eqs'', asserts'@asserts'', annots'@annots''
    else 
      (* let _ =     Format.eprintf "Not inlining call to %s@." id in *)
      { expr with expr_desc = Expr_appl(id, args', reset)}, 
      locals', 
      eqs', 
      asserts',
      annots'

  (* For other cases, we just keep the structure, but convert sub-expressions *)
  | Expr_const _ 
  | Expr_ident _ -> expr, locals, [], [], []
  | Expr_tuple el -> 
    let el', l', eqs', asserts', annots' = inline_tuple el in
    { expr with expr_desc = Expr_tuple el' }, l', eqs', asserts', annots'
  | Expr_ite (g, t, e) ->
    let g', t', e', l', eqs', asserts', annots' = inline_triple g t e in
    { expr with expr_desc = Expr_ite (g', t', e') }, l', eqs', asserts', annots'
  | Expr_arrow (e1, e2) ->
    let e1', e2', l', eqs', asserts', annots' = inline_pair e1 e2 in
    { expr with expr_desc = Expr_arrow (e1', e2') } , l', eqs', asserts', annots'
  | Expr_fby (e1, e2) ->
    let e1', e2', l', eqs', asserts', annots' = inline_pair e1 e2 in
    { expr with expr_desc = Expr_fby (e1', e2') }, l', eqs', asserts', annots'
  | Expr_array el ->
    let el', l', eqs', asserts', annots' = inline_tuple el in
    { expr with expr_desc = Expr_array el' }, l', eqs', asserts', annots'
  | Expr_access (e, dim) ->
    let e', l', eqs', asserts', annots' = inline_expr e locals node nodes in 
    { expr with expr_desc = Expr_access (e', dim) }, l', eqs', asserts', annots'
  | Expr_power (e, dim) ->
    let e', l', eqs', asserts', annots' = inline_expr e locals node nodes in 
    { expr with expr_desc = Expr_power (e', dim) }, l', eqs', asserts', annots'
  | Expr_pre e ->
    let e', l', eqs', asserts', annots' = inline_expr e locals node nodes in 
    { expr with expr_desc = Expr_pre e' }, l', eqs', asserts', annots'
  | Expr_when (e, id, label) ->
    let e', l', eqs', asserts', annots' = inline_expr e locals node nodes in 
    { expr with expr_desc = Expr_when (e', id, label) }, l', eqs', asserts', annots'
  | Expr_merge (id, branches) ->
    let el, l', eqs', asserts', annots' = inline_tuple (List.map snd branches) in
    let branches' = List.map2 (fun (label, _) v -> label, v) branches el in
    { expr with expr_desc = Expr_merge (id, branches') }, l', eqs', asserts', annots'

and inline_node ?(selection_on_annotation=false) node nodes =
  try copy_node (Hashtbl.find inline_table node.node_id)
  with Not_found ->
  let inline_expr = inline_expr ~selection_on_annotation:selection_on_annotation in
  let new_locals, eqs, asserts, annots = 
    List.fold_left (fun (locals, eqs, asserts, annots) eq ->
      let eq_rhs', locals', new_eqs', asserts', annots' = 
	inline_expr eq.eq_rhs locals node nodes 
      in
      locals', { eq with eq_rhs = eq_rhs' }::new_eqs'@eqs, asserts'@asserts, annots'@annots
    ) (node.node_locals, [], node.node_asserts, node.node_annot) (get_node_eqs node)
  in
  let inlined = 
  { node with
    node_locals = new_locals;
    node_stmts = List.map (fun eq -> Eq eq) eqs;
    node_asserts = asserts;
    node_annot = annots;
  }
  in
  begin
    (*Format.eprintf "inline node:<< %a@.>>@." Printers.pp_node inlined;*)
    Hashtbl.add inline_table node.node_id inlined;
    inlined
  end

let inline_all_calls node nodes =
  let nd = match node.top_decl_desc with Node nd -> nd | _ -> assert false in
  { node with top_decl_desc = Node (inline_node nd nodes) }
    




let witness filename main_name orig inlined type_env clock_env =
  let loc = Location.dummy_loc in
  let rename_local_node nodes prefix id =
    if List.exists (check_node_name id) nodes then
      prefix ^ id 
    else
      id
  in
  let main_orig_node = match (List.find (check_node_name main_name) orig).top_decl_desc with
  Node nd -> nd | _ -> assert false in
  
  let orig_rename = rename_local_node orig "orig_" in
  let inlined_rename = rename_local_node inlined "inlined_" in
  let identity = (fun x -> x) in
  let is_node top = match top.top_decl_desc with Node _ -> true | _ -> false in
  let orig = rename_prog orig_rename identity identity orig in
  let inlined = rename_prog inlined_rename identity identity inlined in
  let nodes_origs, others = List.partition is_node orig in
  let nodes_inlined, _ = List.partition is_node inlined in

  (* One ok_i boolean variable  per output var *)
  let nb_outputs = List.length main_orig_node.node_outputs in
  let ok_ident = "OK" in
  let ok_i = List.map (fun id ->
    mkvar_decl 
      loc 
      (Format.sprintf "%s_%i" ok_ident id,
       {ty_dec_desc=Tydec_bool; ty_dec_loc=loc},
       {ck_dec_desc=Ckdec_any; ck_dec_loc=loc},
       false,
       None)
  ) (Utils.enumerate nb_outputs) 
  in

  (* OK = ok_1 and ok_2 and ... ok_n-1 *)
  let ok_output = mkvar_decl 
    loc 
    (ok_ident,
     {ty_dec_desc=Tydec_bool; ty_dec_loc=loc},
     {ck_dec_desc=Ckdec_any; ck_dec_loc=loc},
     false,
     None)
  in
  let main_ok_expr =
    let mkv x = mkexpr loc (Expr_ident x) in
    match ok_i with
    | [] -> assert false
    | [x] -> mkv x.var_id 
    | hd::tl -> 
      List.fold_left (fun accu elem -> 
	mkpredef_call loc "&&" [mkv elem.var_id; accu]
      ) (mkv hd.var_id) tl
  in

  (* Building main node *)

  let ok_i_eq =
    { eq_loc = loc;
      eq_lhs = List.map (fun v -> v.var_id) ok_i;
      eq_rhs = 
	let inputs = expr_of_expr_list  loc (List.map (fun v -> mkexpr loc (Expr_ident v.var_id)) main_orig_node.node_inputs) in
	let call_orig = 
	  mkexpr loc (Expr_appl ("orig_" ^ main_name, inputs, None)) in
	let call_inlined = 
	  mkexpr loc (Expr_appl ("inlined_" ^ main_name, inputs, None)) in
	let args = mkexpr loc (Expr_tuple [call_orig; call_inlined]) in 
	mkexpr loc (Expr_appl ("=", args, None))
    } in
  let ok_eq =
    { eq_loc = loc;
      eq_lhs = [ok_ident];
      eq_rhs = main_ok_expr;
    } in
  let main_node = {
    node_id = "check";
    node_type = Types.new_var ();
    node_clock = Clocks.new_var true;
    node_inputs = main_orig_node.node_inputs;
    node_outputs = [ok_output];
    node_locals = ok_i;
    node_gencalls = [];
    node_checks = [];
    node_asserts = [];
    node_stmts = [Eq ok_i_eq; Eq ok_eq];
    node_dec_stateless = false;
    node_stateless = None;
    node_spec = Some 
      {requires = []; 
       ensures = [mkeexpr loc (mkexpr loc (Expr_ident ok_ident))];
       behaviors = [];
       spec_loc = loc
      };
    node_annot = [];
  }
  in
  let main = [{ top_decl_desc = Node main_node; top_decl_loc = loc; top_decl_owner = filename; top_decl_itf = false }] in
  let new_prog = others@nodes_origs@nodes_inlined@main in
(*
  let _ = Typing.type_prog type_env new_prog in
  let _ = Clock_calculus.clock_prog clock_env new_prog in
*)
   
  let witness_file = (Options.get_witness_dir filename) ^ "/" ^ "inliner_witness.lus" in
  let witness_out = open_out witness_file in
  let witness_fmt = Format.formatter_of_out_channel witness_out in
  begin
    List.iter (fun vdecl -> Typing.try_unify Type_predef.type_bool vdecl.var_type vdecl.var_loc) (ok_output::ok_i);
    Format.fprintf witness_fmt
      "(* Generated lustre file to check validity of inlining process *)@.";
    Printers.pp_prog witness_fmt new_prog;
    Format.fprintf witness_fmt "@.";
    ()
  end (* xx *)

let global_inline basename prog type_env clock_env =
  (* We select the main node desc *)
  let main_node, other_nodes, other_tops = 
    List.fold_right
      (fun top (main_opt, nodes, others) -> 
	match top.top_decl_desc with 
	| Node nd when nd.node_id = !Options.main_node -> 
	  Some top, nodes, others
	| Node _ -> main_opt, top::nodes, others
	| _ -> main_opt, nodes, top::others) 
      prog (None, [], []) 
  in
  (* Recursively each call of a node in the top node is replaced *)
  let main_node = Utils.desome main_node in
  let main_node' = inline_all_calls main_node other_nodes in
  let res = List.map (fun top -> if check_node_name !Options.main_node top then main_node' else top) prog in
  res

let local_inline basename prog type_env clock_env =
  let local_anns = Annotations.get_expr_annotations keyword in
  if local_anns != [] then (
    let nodes_with_anns = List.fold_left (fun accu (k, _) -> ISet.add k accu) ISet.empty local_anns in
    ISet.iter (fun node_id -> Format.eprintf "Node %s has local expression annotations@." node_id) nodes_with_anns;
    List.fold_right (fun top accu -> 
      ( match top.top_decl_desc with
      | Node nd when ISet.mem nd.node_id nodes_with_anns ->
	{ top with top_decl_desc = Node (inline_node ~selection_on_annotation:true nd prog) }
      | _ -> top
      )::accu) prog []
    
)
 else
  prog


(* Local Variables: *)
(* compile-command:"make -C .." *)
(* End: *)
