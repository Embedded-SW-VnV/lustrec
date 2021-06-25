module type S = sig
  val name : string

  val activate : unit -> unit

  val is_active : unit -> bool

  val options : (string * Arg.spec * string) list

  val get_normalization_params : unit -> Normalization.param_t

  val run :
    basename:string ->
    Lustre_types.program_t ->
    Machine_code_types.machine_t list ->
    unit
end
