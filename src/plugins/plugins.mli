open Utils
open Lustre_types

val inline_annots: (ident -> ident) -> expr_annot list -> expr_annot list

val check_force_stateful: unit -> bool

val c_backend_main_loop_body_prefix: string -> string -> Format.formatter -> unit -> unit
val c_backend_main_loop_body_suffix: Format.formatter -> unit -> unit
