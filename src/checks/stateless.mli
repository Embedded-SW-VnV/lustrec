open Utils
open Lustre_types

type error =
  | Stateful_kwd of ident
  | Stateful_imp of ident
  | Stateful_ext_C of ident

exception Error of Location.t * error

val check_node: top_decl -> bool
val check_prog: program_t -> unit
val force_prog: program_t -> unit
val check_compat: top_decl list -> unit

val pp_error: Format.formatter -> error -> unit
