open Lustre_types
open Machine_code_types

val translate_to_c: bool -> string -> program_t -> machine_t list -> dep_t list -> unit

val print_c_header: string -> unit
