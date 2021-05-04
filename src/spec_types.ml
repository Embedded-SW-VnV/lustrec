open Lustre_types

type state_t =
  | In
  | Out

type expression_t =
  | Cst of constant
  | Var of var_decl
  | Instance of state_t * ident
  | Memory of state_t * ident

type predicate_t =
  | Atom of expression_t
  | Equal of predicate_t * predicate_t
  | Imply of predicate_t * predicate_t
  | Exists of var_decl list * predicate_t list
  | Forall of var_decl list * predicate_t list

type transition_t = {
  tname: node_desc;
  tindex: int;
  tlocals: var_decl list;
  toutputs: var_decl list;
  tpredicate: predicate_t list;
}
