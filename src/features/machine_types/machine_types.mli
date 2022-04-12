open Utils
open Format
open Lustre_types

val is_exportable : var_decl -> bool

val has_machine_type : unit -> bool

val is_specified : var_decl -> bool

val is_active : bool

val pp_var_type : formatter -> var_decl -> unit

val pp_c_var_type : formatter -> var_decl -> unit

val load : program_t -> unit

(* Typing the expression (vars = expr) in node *)
val type_def : ident * var_decl list -> var_decl list -> expr -> unit

module ConvTypes : Typing.EXPR_TYPE_HUB

val get_specified_type : var_decl -> ConvTypes.type_expr

val type_name : ConvTypes.type_expr -> ident

val keywords : string list
