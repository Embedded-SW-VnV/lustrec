open Utils

type t =
  | Main_not_found
  | Main_wrong_kind
  | No_main_specified
  | Unbound_symbol of ident
  | Already_bound_symbol of ident
  | Unknown_library of ident
  | Wrong_number of ident
  | AlgebraicLoop
  | LoadError of string

exception Error of Location.t * t

val return_code: t -> int

val pp: Format.formatter -> t -> unit
val pp_error: Location.t -> (Format.formatter -> unit) -> unit
val pp_warning: Location.t -> (Format.formatter -> unit) -> unit
