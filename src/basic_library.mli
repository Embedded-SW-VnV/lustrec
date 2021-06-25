open Utils

val internal_funs: ident list
val arith_funs: ident list
val bool_funs: ident list
val rel_funs: ident list
val eval_dim_env: (Dimension.dim_desc list -> Dimension.dim_desc) Env.t
val is_homomorphic_fun: ident -> bool
val is_internal_fun: ident -> Types.t list -> bool
val is_expr_internal_fun: Lustre_types.expr -> bool
val is_value_internal_fun: Machine_code_types.value_t -> bool
val is_stateless_fun: ident -> bool

val type_env: Types.t Env.t
val clock_env: Clocks.t Env.t

val partial_eval: ident -> Lustre_types.expr -> Lustre_types.expr option -> Lustre_types.expr_desc
