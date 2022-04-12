open Utils
open Lustre_types
open Machine_code_types
open Format

val pp_emf_cst_or_var_list : machine_t -> formatter -> value_t list -> unit

val pp_emf_cst_or_var : machine_t -> formatter -> value_t -> unit

val pp_var_name : formatter -> var_decl -> unit

val pp_protect : formatter -> (formatter -> unit) -> unit

val pp_var_string : formatter -> ident -> unit

val pp_emf_vars_decl : formatter -> var_decl list -> unit

val pp_tag_id : formatter -> ident -> unit

val pp_emf_expr : formatter -> expr -> unit

val pp_emf_eexpr : formatter -> eexpr -> unit

val pp_emf_eexprs : formatter -> eexpr list -> unit

val pp_emf_list :
  ?eol:(unit, formatter, unit) Stdlib.format ->
  (formatter -> 'a -> unit) ->
  formatter ->
  'a list ->
  unit

val pp_emf_typedef : formatter -> Lustre_types.top_decl -> unit

val pp_emf_top_const : formatter -> Lustre_types.top_decl -> unit

val reset_name : ident -> ident

val get_expr_vars : value_t -> Corelang.VSet.t

val is_imported_node : ident -> machine_t -> bool
