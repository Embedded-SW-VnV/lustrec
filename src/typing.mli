open Lustre_types

val type_const : ?is_annot:bool -> Location.t -> constant -> Types.t

val type_node : Types.t Env.t -> node_desc -> Location.t -> Types.t Env.t

module type EXPR_TYPE_HUB = sig
  type type_expr

  val import : Types.t -> type_expr

  val export : type_expr -> Types.t
end

module Make
    (T : Types.S)
    (Expr_type_hub : EXPR_TYPE_HUB with type type_expr = T.t) : sig
  val type_expr :
    ?is_annot:bool -> T.t Env.t * 'a -> bool -> bool -> expr -> T.t

  val generalize : T.t -> unit
end

val try_unify :
  ?sub:bool -> ?semi:bool -> Types.t -> Types.t -> Location.t -> unit

val type_var_decl_list : 'a -> Types.t Env.t -> var_decl list -> Types.t Env.t

val type_prog : Types.t Env.t -> program_t -> Types.t Env.t

val check_typedef_compat : top_decl list -> unit

val check_env_compat : top_decl list -> Types.t Env.t -> Types.t Env.t -> unit

val uneval_prog_generics : program_t -> unit

(* Equality on ground types only *)
(* Should be used between local variables which must have a ground type *)
val eq_ground : Types.t -> Types.t -> bool
