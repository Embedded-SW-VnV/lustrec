open Utils
open Machine_code_types

(** Print the package declaration(ads) of a machine. It requires the list of
    all typed instance. A typed submachine is a (ident, typed_machine) with -
    ident: the name - typed_machine: a (substitution, machine) with - machine:
    the submachine struct - substitution the instanciation of all its
    polymorphic types. @param fmt the formater to print on @param
    typed_submachines list of all typed submachines of this machine @param m
    the machine **)
val pp_file: Format.formatter -> (ident * ((tag * Types.t) list * machine_t)) list
                                 * ((machine_t option * ident list) * machine_t) -> unit
