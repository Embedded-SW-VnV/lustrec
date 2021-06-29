open Lustre_types

val check_main: unit -> unit

(* Loading Lus/Lusi file and filling type tables with parsed functions/nodes *)
val parse: string -> string -> program_t

val check_compatibility: program_t * Types.t Env.t * Clocks.t Env.t ->
  top_decl list * Types.t Env.t * Clocks.t Env.t -> unit

val update_vdecl_parents_prog: program_t -> unit

val expand_automata: program_t -> program_t

(* Process each node/imported node and introduce the associated contract node *)
val resolve_contracts: program_t -> program_t

val force_stateful_decls: program_t -> unit

val check_stateless_decls: program_t -> unit

val type_decls: Types.t Env.t -> program_t -> Types.t Env.t

val clock_decls: Clocks.t Env.t -> program_t -> Clocks.t Env.t

val create_dest_dir: unit -> unit

val track_exception: unit -> unit
