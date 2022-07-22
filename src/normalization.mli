open Lustre_types

type param_t =
  {
    unfold_arrow_active: bool;
    force_alias_ite: bool;
    force_alias_internal_fun: bool;
  }


val mk_expr_alias_opt: bool -> (ident * var_decl list) -> (eq list * var_decl list)-> expr -> (eq list * var_decl list) * expr
val normalize_prog: param_t -> program_t -> program_t
