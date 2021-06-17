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

open Lustre_types
open Dimension
open Utils
open ISet
module Live = Map.Make (Int)

let assigned s eq = union s (of_list eq.eq_lhs)

let rec occur_dim_expr s d =
  match d.dim_desc with
  | Dident x ->
    add x s
  | Dappl (_, ds) ->
    List.fold_left occur_dim_expr s ds
  | Dite (e, t, f) ->
    occur_dim_expr (occur_dim_expr (occur_dim_expr s e) t) f
  | Dlink d ->
    occur_dim_expr s d
  | _ ->
    s

let rec occur_expr s e =
  match e.expr_desc with
  | Expr_ident x ->
    add x s
  | Expr_tuple es | Expr_array es ->
    List.fold_left occur_expr s es
  | Expr_ite (e, t, f) ->
    occur_expr (occur_expr (occur_expr s e) t) f
  | Expr_arrow (e1, e2) | Expr_fby (e1, e2) ->
    occur_expr (occur_expr s e1) e2
  | Expr_access (e, d) | Expr_power (e, d) ->
    occur_expr (occur_dim_expr s d) e
  | Expr_pre e ->
    occur_expr s e
  | Expr_when (e, x, _) ->
    occur_expr (add x s) e
  | Expr_merge (x, les) ->
    List.fold_left (fun s (_, e) -> occur_expr s e) (add x s) les
  | Expr_appl (_, e, r) ->
    occur_expr (match r with Some r -> occur_expr s r | None -> s) e
  | _ ->
    s

let occur s eq = occur_expr s eq.eq_rhs

let live : (ident, ISet.t Live.t) Hashtbl.t = Hashtbl.create 32

let of_var_decls = List.fold_left (fun s v -> add v.var_id s) empty

let set_live_of nid outputs locals sorted_eqs =
  let outputs = of_var_decls outputs in
  let locals = of_var_decls locals in
  let vars = union locals outputs in
  let no_occur_after i =
    let occ, _ =
      List.fold_left
        (fun (s, j) eq -> if j <= i then s, j + 1 else occur s eq, j + 1)
        (empty, 0) sorted_eqs
    in
    diff locals occ
  in
  let l, _, _ =
    List.fold_left
      (fun (l, asg, i) eq ->
        let asg = inter (assigned asg eq) vars in
        let noc = no_occur_after i in
        let liv = diff asg noc in
        Live.add (i + 1) liv l, asg, i + 1)
      (Live.add 0 empty Live.empty, empty, 0)
      sorted_eqs
  in
  Log.report ~level:6 (fun fmt ->
      Format.(
        fprintf fmt "Live variables of %s: %a@;@;" nid
          (pp_print_list ~pp_open_box:pp_open_vbox0 (fun fmt (i, l) ->
               fprintf fmt "%i: %a" i pp_iset l))
          (Live.bindings l)));
  Hashtbl.add live nid l

let live_i nid i = Live.find i (Hashtbl.find live nid)

let inter_live_i_with nid i =
  let li = live_i nid i in
  List.filter (fun v -> mem v.var_id li)

let existential_vars nid i eq =
  let li' = live_i nid (i - 1) in
  let li = live_i nid i in
  let d = diff (union li' (assigned empty eq)) li in
  List.filter (fun v -> mem v.var_id d)
