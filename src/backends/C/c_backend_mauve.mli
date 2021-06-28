open Format
open Machine_code_types

val print_mauve_header: formatter -> string -> unit
val print_mauve_shell: formatter -> machine_t -> unit
val print_mauve_core: formatter -> machine_t -> unit
val print_mauve_fsm: formatter -> machine_t -> unit
