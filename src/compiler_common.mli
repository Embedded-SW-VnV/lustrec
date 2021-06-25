open Lustre_types

val check_main: unit -> unit

(* Loading Lus/Lusi file and filling type tables with parsed functions/nodes *)
val parse: string -> string -> program_t

val check_compatibility: program_t * Types.t Env.t * Clocks.t Env.t ->
  top_decl list * Types.t Env.t * Clocks.t Env.t -> unit

val update_vdecl_parents_prog: program_t -> unit

val expand_automata: program_t -> program_t
