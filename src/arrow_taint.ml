open Lustre_types
open Corelang

let find_taint_arrow eqs locals (x, _) =
  let ck_x = x.var_clock in
  x,
  List.find_map (fun eq -> match eq.eq_lhs, eq.eq_rhs.expr_desc with
      | [y], Expr_arrow _ ->
        let o_ck_y = List.find_map (fun (v, _) ->
            if v.var_id = y then Some v.var_clock else None) locals
        in
        begin match o_ck_y with
          | Some ck_y ->
            (* if (x.var_id = "__if_multi_test_9") then *)
            (*   Format.printf "%s :: %a (%d) - %s :: %a (%d)\n" x.var_id Clocks.pp ck_x ck_x.cid y Clocks.pp ck_y ck_y.cid; *)
            if Clocks.equal ck_y ck_x then Some y else None
          | _ -> None
        end
      | _ -> None) eqs

let arrow_taint_node node =
  let eqs, auts = get_node_eqs node in
  if auts != [] then assert false;
  (* Automata should be expanded by now. *)
  let node_locals = List.map (find_taint_arrow eqs node.node_locals) node.node_locals in
  { node with node_locals }

let arrow_taint_inode nd =
  match nd.nodei_spec with
  | None | Some (NodeSpec _) -> nd
  | Some (Contract _) -> assert false

let arrow_taint_decl decl =
  match decl.top_decl_desc with
  | Node nd ->
      let decl' = { decl with top_decl_desc = Node (arrow_taint_node nd) } in
      update_node nd.node_id decl';
      decl'
  | ImportedNode nd ->
      let decl' =
        { decl with top_decl_desc = ImportedNode (arrow_taint_inode nd) }
      in
      update_node nd.nodei_id decl';
      decl'
  | Include _ | Open _ | Const _ | TypeDef _ -> decl

let arrow_taint_prog decls =
  List.map arrow_taint_decl decls
