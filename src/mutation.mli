open Utils
open Format
open Lustre_types

type mutant_t =
  | Boolexpr of int
  | Pre of int
  | Op of string * int * string
  | IncrIntCst of int
  | DecrIntCst of int
  | SwitchIntCst of int * int

val pp_directive_json: formatter -> mutant_t -> unit

val pp_directive: formatter -> mutant_t -> unit

val pp_loc_json: formatter -> ident * ident list * Location.t -> unit

val mutate: int -> program_t -> (mutant_t * (ident * ident list * Location.t) * program_t) list
