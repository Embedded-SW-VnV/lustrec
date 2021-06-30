open Utils
open Lustre_types

val compute_unused_variables : node_desc -> IdentDepGraph.t -> ISet.t

type fanin = (ident, tag) Hashtbl.t

(* computes the in-degree for each local variable of node [n], according to dep
   graph [g]. *)
val compute_fanin : node_desc -> IdentDepGraph.t -> fanin

val pp_fanin : Format.formatter -> fanin -> unit

val compute_reuse_policy :
  node_desc ->
  ident list list ->
  Causality.Disjunction.disjoint_map ->
  IdentDepGraph.t ->
  (ident, var_decl) Hashtbl.t

(* replace variable [v] by [v'] in graph [g]. [v'] is a dead variable *)
val replace_in_dep_graph : ident -> ident -> IdentDepGraph.t -> unit
