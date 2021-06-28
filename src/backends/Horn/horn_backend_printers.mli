open Format
open Lustre_types
open Machine_code_types

val pp_horn_var: machine_t -> formatter -> var_decl -> unit
val pp_xml_expr: formatter -> expr -> unit
val print_sfunction: machine_t list -> formatter -> machine_t -> unit
val print_machine: machine_t list -> formatter -> machine_t -> unit
