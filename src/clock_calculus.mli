open Lustre_types

val clock_node: Clocks.t Env.t -> Location.t -> node_desc -> Clocks.t Env.t

val compute_root_clock: Clocks.t -> Clocks.t

val clock_prog: Clocks.t Env.t -> program_t -> Clocks.t Env.t

val check_env_compat: top_decl list -> Clocks.t Env.t -> Clocks.t Env.t -> unit
