open Utils
open Lustre_types

type schedule_report =
{
  (* the scheduled node *)
  node : node_desc;
  (* a schedule computed wrt the dependency graph *)
  schedule : ident list list;
  (* the set of unused variables (no output or mem depends on them) *)
  unused_vars : ISet.t;
  (* the table mapping each local var to its in-degree *)
  fanin_table : (ident, int) Hashtbl.t;
  (* the dependency graph *)
  dep_graph   : IdentDepGraph.t;
  (* the table mapping each assignment to a reusable variable *)
  (*reuse_table : (ident, var_decl) Hashtbl.t*)
}
 
