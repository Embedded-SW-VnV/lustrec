open Utils
open Format
open Lustre_types
open Machine_code_types

val unfoldable_value: Machine_code_types.value_t -> bool
val inject_prog: program_t -> program_t

val mpfr_t: string

val mpfr_rnd: unit -> string
val mpfr_prec: unit -> int

val is_homomorphic_fun: ident -> bool

val pp_inject_init: (formatter -> 'a -> unit) -> formatter -> 'a -> unit
val pp_inject_clear: (formatter -> 'a -> unit) -> formatter -> 'a -> unit
val pp_inject_assign: (formatter -> value_t -> unit) -> formatter -> value_t * value_t -> unit
val pp_inject_real: (formatter -> 'a -> unit) -> (formatter -> 'b -> unit) -> formatter -> 'a * 'b -> unit
