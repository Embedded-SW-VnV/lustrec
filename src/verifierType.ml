module type S =
sig
  val name: string
  val activate: unit -> unit
  val is_active: unit -> bool
  val options: (string * Arg.spec * string) list
  val get_normalization_params: unit -> Normalization.param_t
  val run: string -> Lustre_types.program_t -> Machine_code_types.machine_t list -> unit 
end

module Default =
  struct

    let get_normalization_params () = {
    Normalization.unfold_arrow_active = true;
    force_alias_ite = false;
    force_alias_internal_fun = false;
  }

  end
