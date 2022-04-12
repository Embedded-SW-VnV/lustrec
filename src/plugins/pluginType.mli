module type S = sig
  val name : string

  val activate : unit -> unit

  val usage : Format.formatter -> unit

  val options : Options_management.options_spec

  val init : unit -> unit

  val check_force_stateful : unit -> bool

  val refine_machine_code :
    Lustre_types.top_decl list ->
    Machine_code_types.machine_t list ->
    Machine_code_types.machine_t list

  val c_backend_main_loop_body_prefix :
    string -> string -> Format.formatter -> unit -> unit

  val c_backend_main_loop_body_suffix : Format.formatter -> unit -> unit
end

module Default : S
