module type S = sig
  val name : string

  val activate : unit -> unit

  val is_active : unit -> bool

  val options : Options_management.options_spec

  val get_normalization_params : unit -> Normalization.param_t

  val run :
    basename:string ->
    Lustre_types.program_t ->
    Machine_code_types.machine_t list ->
    unit
end
