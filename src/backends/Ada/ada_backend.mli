(** Main function of the Ada backend. It calls all the subfunction creating all
    the file and fill them with Ada code representing the machines list given.
    @param basename name of the lustre file @param prog list of machines to
    translate **)
val translate_to_ada: string -> Machine_code_types.machine_t list -> unit
