open Utils
open Machine_code_types

val cex_computation: machine_t list -> Format.formatter -> ident -> machine_t -> unit
val get_cex: machine_t list -> Format.formatter -> machine_t -> unit
val collecting_semantics: machine_t list -> Format.formatter -> ident -> machine_t -> unit
val check_prop: machine_t list -> Format.formatter -> machine_t -> unit
