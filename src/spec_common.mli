open Utils
open Lustre_types
open Spec_types

val type_of_l_value : 'a expression_t -> Types.t

val mk_conditional_tr : 'a -> 'a formula_t -> 'a formula_t -> 'a formula_t

val mk_branch_tr : var_decl -> (ident * 'a formula_t) list -> 'a formula_t

val mk_assign_tr : var_decl -> 'a -> 'a formula_t

val mk_memory_pack : ?i:int -> ?inst:ident -> ident -> 'a formula_t

val mk_transition :
  ?mems:ISet.t ->
  ?insts:ident IMap.t ->
  ?r:'a ->
  ?i:int ->
  ?inst:ident ->
  bool ->
  ident ->
  'a list ->
  'a formula_t

val mk_state_variable_pack : var_decl -> 'a formula_t

val mk_state_assign_tr : var_decl -> 'a -> 'a formula_t

val red : 'a formula_t -> 'a formula_t
