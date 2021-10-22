open Utils
open Lustre_types

type error =
  | DataCycle of ident list list
  (* multiple failed partitions at once *)
  | NodeCycle of ident list

exception Error of error

val pp_error : Format.formatter -> error -> unit

val world : ident

module NodeDep : sig
  val dependence_graph : program_t -> IdentDepGraph.t

  val filter_static_inputs : var_decl list -> expr list -> Dimension.t list

  val compute_generic_calls : program_t -> unit

  val get_callee : expr -> (ident * expr list) option

  val get_calls : (ident -> bool) -> node_desc -> expr list
end

(* Look for cycles in a dependency graph *)
module CycleDetection : sig
  val check_cycles : IdentDepGraph.t -> unit
end

(* A module to sort dependencies among local variables when relying on clocked
   declarations *)
module VarClockDep : sig
  val sort : var_decl list -> var_decl list
end

module ExprDep : sig
  (* instance vars represent node instance calls, they are not part of the
     program/schedule, but used to simplify causality analysis *)
  val mk_instance_var : ident -> ident

  val mk_read_var : ident -> ident

  val is_instance_var : ident -> bool

  val is_ghost_var : ident -> bool

  val is_read_var : ident -> bool

  val undo_instance_var : ident -> ident

  val undo_read_var : ident -> ident

  val node_eq_equiv : node_desc -> (ident, ident) Hashtbl.t

  val node_input_variables : node_desc -> ISet.t

  val node_local_variables : node_desc -> ISet.t

  val node_output_variables : node_desc -> ISet.t

  val node_memory_variables : node_desc -> ISet.t
end

(* Module used to compute static disjunction of variables based upon their
   clocks. *)
module Disjunction : sig
  module CISet : Set.S with type elt = var_decl

  (* map: var |-> list of disjoint vars, sorted in increasing branch length
     order, maybe removing shorter branches *)
  type disjoint_map = (ident, CISet.t) Hashtbl.t

  val pp_ciset : Format.formatter -> CISet.t -> unit

  val clock_disjoint_map : var_decl list -> disjoint_map

  val pp_disjoint_map : Format.formatter -> disjoint_map -> unit
end

(* Tests whether [v] is a root of graph [g], i.e. a source *)
val is_graph_root : ident -> IdentDepGraph.t -> bool

(* Computes the set of graph roots, i.e. the sources of acyclic graph [g] *)
val graph_roots : IdentDepGraph.t -> ident list

(* Takes a node and return a pair (node', graph) where node' is node rebuilt
   with the equations enriched with new ones introduced to "break cycles" *)
val global_dependency : node_desc -> node_desc * IdentDepGraph.t

val pp_dep_graph : Format.formatter -> IdentDepGraph.t -> unit
