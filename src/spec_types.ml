open Utils
open Lustre_types

type register_t = ResetFlag | StateVar of var_decl

type 'a expression_t =
  | Val of 'a
  | Tag of ident * Types.t
  | Var of var_decl
  | Memory of register_t

type 'a predicate_t =
  | Transition :
      bool (* stateless *)
      * ident (* node name *)
      * ident option
      (* instance *)
      * int option
      (* transition index *)
      * 'a expression_t list
      (* variables *)
      * bool (* reset *)
      * Utils.ISet.t (* memory footprint *)
      * ident Utils.IMap.t
      (* memory instances footprint *)
      -> 'a predicate_t
  | Reset of ident * ident * 'a
  | MemoryPack of ident * ident option * int option
  | MemoryPackBase of ident
  | Initialization
  | ResetCleared of ident
  | GhostAssign of var_decl * var_decl

type 'a formula_t =
  | True
  | False
  | Equal of 'a expression_t * 'a expression_t
  | GEqual of 'a expression_t * 'a expression_t
  | And of 'a formula_t list
  | Or of 'a formula_t list
  | Imply of 'a formula_t * 'a formula_t
  | Exists of var_decl list * 'a formula_t
  | Forall of var_decl list * 'a formula_t
  | Ternary of 'a expression_t * 'a formula_t * 'a formula_t
  | Predicate : 'a predicate_t -> 'a formula_t
  | StateVarPack of register_t * bool (* tainted or not *)
  | ExistsMem of ident * 'a formula_t * 'a formula_t
  | Value of 'a

(* type 'a simulation_t = {
 *   sname: node_desc;
 *   sindex: option int;
 *   sformula: 'a formula_t;
 * } *)

type 'a memory_pack_t = {
  mpname : node_desc;
  mpindex : int option;
  mpformula : 'a formula_t;
}

type 'a transition_t = {
  tname : node_desc;
  tindex : int option;
  tvars : var_decl list;
  tformula : 'a formula_t;
  tmem_footprint : Utils.ISet.t;
  tinst_footprint : ident Utils.IMap.t;
}
