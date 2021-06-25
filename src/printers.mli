open Format
open Lustre_types

val pp_expr: formatter -> expr -> unit
val pp_eexpr: formatter -> eexpr -> unit
val pp_node: formatter -> node_desc -> unit
val pp_const: formatter -> constant -> unit
val pp_var: formatter -> var_decl -> unit
val pp_node_eq: formatter -> eq -> unit
val pp_node_eqs: formatter -> eq list -> unit
val pp_spec: formatter -> contract_desc -> unit
val pp_expr_annot: formatter -> expr_annot -> unit
val pp_short_decl: formatter -> top_decl -> unit
val pp_const_decl: formatter -> const_desc -> unit
val pp_var_type_dec_desc: formatter -> type_dec_desc -> unit
val pp_typedef: formatter -> typedef_desc -> unit
val pp_prog: formatter -> program_t -> unit
