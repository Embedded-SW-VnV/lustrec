open Lustre_types
open Machine_code_types
open Corelang
open Utils

let rec add_expr_dependencies g x e = match e.value_desc with
  | Var y ->
    let y' = y.var_id in
    if y' <> x then
      IdentDepGraph.add_edge g x y'
  | Fun (_, es)
  | Array es ->
    List.iter (add_expr_dependencies g x) es
  | Access (e1, e2)
  | Power (e1, e2) ->
    add_expr_dependencies g x e1;
    add_expr_dependencies g x e2
  | _ -> ()

let rec add_instr_dependencies g deps instr = match get_instr_desc instr with
  | MLocalAssign (x, e)
  | MStateAssign (x, e) ->
    add_expr_dependencies g x.var_id e;
    List.iter (add_expr_dependencies g x.var_id) deps
  | MStep (xs, i, es) ->
    List.iter (fun x ->
        IdentDepGraph.add_edge g x.var_id i;
        List.iter (add_expr_dependencies g x.var_id) es;
        List.iter (add_expr_dependencies g x.var_id) deps) xs;
    List.iter (add_expr_dependencies g i) deps
  | MSetReset i
  | MNoReset i ->
    List.iter (add_expr_dependencies g i) deps
  | MBranch (e, hl) ->
    List.iter (fun (_, l) -> List.iter (add_instr_dependencies g (e :: deps)) l) hl
  | _ -> ()

let dep_graph m =
  let g = IdentDepGraph.create () in
  List.iter (add_instr_dependencies g []) m.mstep.step_instrs;
  List.iter (fun x -> IdentDepGraph.add_edge g Causality.world x.var_id) m.mstep.step_outputs;
  g

(* computes the cone of influence of a given [var] wrt a dependency graph
   [g]. *)
let cone_of_influence g var =
  (*Format.printf "DEBUG coi: %s@." var;*)
  let frontier = ref (ISet.add var ISet.empty) in
  let explored = ref ISet.empty in
  let coi = ref ISet.empty in
  while not (ISet.is_empty !frontier) do
    let head = ISet.min_elt !frontier in
    frontier := ISet.remove head !frontier;
    explored := ISet.add head !explored;
    if head <> var then coi := ISet.add head !coi;
    List.iter
      (fun s ->
        if not (ISet.mem s !explored) then frontier := ISet.add s !frontier)
      (IdentDepGraph.succ g head)
  done;
  !coi

let compute_unused_variables m =
  let g = dep_graph m in
  (* Format.printf "graph of %s: %a@." m.mname.node_id Causality.pp_dep_graph g; *)
  List.fold_left
    (fun unused x ->
       let coi = cone_of_influence g x.var_id in
       (* Format.printf "unused: %a@;coi of %s: %a@." ISet.pp unused x.var_id ISet.pp coi; *)
       ISet.diff unused coi)
    (List.fold_left (fun s v -> ISet.add v.var_id s) ISet.empty m.mstep.step_locals)
    (m.mstep.step_outputs @ m.mmemory)
