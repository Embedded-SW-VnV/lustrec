open Lustre_types
open Machine_code_types
open Corelang
open Utils

let rec add_expr_dependencies inputs g x e = match e.value_desc with
  | Var y ->
    let y' = y.var_id in
    IdentDepGraph.add_edge g x.var_id
      (if List.exists (fun z -> z.var_id = y') inputs
       then Causality.ExprDep.mk_read_var y' else y')
  | Fun (_, es)
  | Array es ->
    List.iter (add_expr_dependencies inputs g x) es
  | Access (e1, e2)
  | Power (e1, e2) ->
    add_expr_dependencies inputs g x e1;
    add_expr_dependencies inputs g x e2
  | _ -> ()

let rec add_instr_dependencies inputs g deps instr = match get_instr_desc instr with
  | MLocalAssign (x, e)
  | MStateAssign (x, e) ->
    add_expr_dependencies inputs g x e;
    List.iter (add_expr_dependencies inputs g x) deps
  | MStep (xs, _, es) ->
    List.iter (fun x ->
        List.iter (add_expr_dependencies inputs g x) es;
        List.iter (add_expr_dependencies inputs g x) deps) xs
  | MBranch (e, hl) ->
    List.iter (fun (_, l) -> List.iter (add_instr_dependencies inputs g (e :: deps)) l) hl
  | _ -> ()

let dep_graph m =
  let g = IdentDepGraph.create () in
  List.iter (add_instr_dependencies m.mstep.step_inputs g []) m.mstep.step_instrs;
  List.iter (fun x -> IdentDepGraph.add_edge g Causality.world x.var_id) m.mstep.step_outputs;
  g

let compute_unused_variables m =
  let g = dep_graph m in
  List.fold_left
    (fun unused x ->
       (* let coi = Liveness.cone_of_influence g x.var_id in *)
       (* Format.printf "unused: %a@;coi of %s: %a@." ISet.pp unused x.var_id ISet.pp coi; *)
       ISet.diff unused (Liveness.cone_of_influence g x.var_id))
    (List.fold_left (fun s v -> ISet.add v.var_id s) ISet.empty (m.mstep.step_locals @ m.mstep.step_inputs))
    m.mstep.step_outputs
