open Utils
open Lustre_types
open Machine_code_types

val inline_annots: (ident -> ident) -> expr_annot list -> expr_annot list

val check_force_stateful: unit -> bool

val c_backend_main_loop_body_prefix: string -> string -> Format.formatter -> unit -> unit
val c_backend_main_loop_body_suffix: Format.formatter -> unit -> unit

val refine_machine_code: program_t -> machine_t list -> machine_t list

val init: unit -> unit

val options: unit -> Options_management.options_spec
