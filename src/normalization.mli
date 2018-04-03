type param_t =
  {
    unfold_arrow_active: bool;
    force_alias_ite: bool;
    force_alias_internal_fun: bool;
  }


val mk_expr_alias_opt: bool -> Lustre_types.node_desc -> (Lustre_types.eq list * Lustre_types.var_decl list)-> Lustre_types.expr -> (Lustre_types.eq list * Lustre_types.var_decl list) * Lustre_types.expr
val normalize_prog: param_t -> Lustre_types.program_t -> Lustre_types.program_t
