open Lustre_types

type state_t =
  | In
  | Out

type 'a expression_t =
  | Val of 'a
  | Tag of ident
  | Var of var_decl
  | Instance of state_t * ident
  | Memory of state_t * ident

type predicate_t =
  (* | Memory_pack *)
  | Clocked_on of ident
  | Transition
  | Initialization

type 'a formula_t =
  | True
  | False
  | Equal of 'a expression_t * 'a expression_t
  | And of 'a formula_t list
  | Or of 'a formula_t list
  | Imply of 'a formula_t * 'a formula_t
  | Exists of var_decl list * 'a formula_t
  | Forall of var_decl list * 'a formula_t
  | Ternary of 'a expression_t * 'a formula_t * 'a formula_t
  | Predicate of predicate_t * 'a expression_t list

(* type 'a simulation_t = {
 *   sname: node_desc;
 *   sindex: option int;
 *   sformula: 'a formula_t;
 * } *)

type 'a transition_t = {
  tname: node_desc;
  tindex: int option;
  tlocals: var_decl list;
  toutputs: var_decl list;
  tformula: 'a formula_t;
}

