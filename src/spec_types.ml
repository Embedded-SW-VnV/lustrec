open Utils
open Lustre_types

type register_t = ResetFlag | StateVar of var_decl

type left_v

type right_v

type ('a, _) expression_t =
  | Val : 'a -> ('a, right_v) expression_t
  | Tag : ident -> ('a, right_v) expression_t
  | Var : var_decl -> ('a, left_v) expression_t
  | Memory : register_t -> ('a, left_v) expression_t

(** TODO: why moving this elsewhere makes the exhaustiveness check fail? *)
let type_of_l_value : type a. (a, left_v) expression_t -> Types.t = function
  | Var v ->
    v.var_type
  | Memory ResetFlag ->
    Type_predef.type_bool
  | Memory (StateVar v) ->
    v.var_type

type 'a predicate_t =
  | Transition :
      ident (* node name *)
      * ident option
      (* instance *)
      * int option
      (* transition index *)
      * ('a, 'b) expression_t list
      (* variables *)
      * bool (* reset *)
      * Utils.ISet.t (* memory footprint *)
      * ident Utils.IMap.t
      (* memory instances footprint *)
      -> 'a predicate_t
  | Reset of ident * ident * 'a
  | MemoryPack of ident * ident option * int option
  | Initialization
  | ResetCleared of ident

type 'a formula_t =
  | True
  | False
  | Equal : ('a, left_v) expression_t * ('a, 'b) expression_t -> 'a formula_t
  | And of 'a formula_t list
  | Or of 'a formula_t list
  | Imply of 'a formula_t * 'a formula_t
  | Exists of var_decl list * 'a formula_t
  | Forall of var_decl list * 'a formula_t
  | Ternary :
      ('a, 'b) expression_t * 'a formula_t * 'a formula_t
      -> 'a formula_t
  | Predicate : 'a predicate_t -> 'a formula_t
  | StateVarPack of register_t
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
