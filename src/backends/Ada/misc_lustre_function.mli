open Utils
open Machine_code_types

val is_machine_statefull: machine_t -> bool
val is_arrow: machine_t -> bool

(** Find all polymorphic type : Types.Tunivar in a machine. @param machine the
    machine @return a list of id corresponding to polymorphic type **)
val find_all_polymorphic_type: machine_t -> int list

(** Test if two types are the same. @param typ1 the first type @param typ2 the
    second type **)
val pp_eq_type: Types.t -> Types.t -> bool

(** Check if a submachine is statefull. @param submachine a submachine @return
    true if the submachine is statefull **)
val is_submachine_statefull: 'a * ('b * machine_t) -> bool

(** Extract from a machine the instance corresponding to the identifier, assume
    that the identifier exists in the instances of the machine.

    @param identifier the instance identifier @param machine a machine @return
    the instance of machine.minstances corresponding to identifier **)
val get_instance: 'a -> ('a * 'b) list -> 'b

val build_if: 'a -> ident -> 'b -> ('c * 'b) list -> bool * 'a * 'b * 'b option

(** Extract from a machine list the one corresponding to the given instance.
    assume that the machine is in the list. @param machines list of all machines
    @param instance instance of a machine @return the machine corresponding to
    hte given instance **)
val get_machine: machine_t list -> 'a * (Lustre_types.top_decl * 'b) -> machine_t

(** Extract from a subinstance that can have polymorphic type the instantiation
    of all its polymorphic type instanciation for a given machine. It searches
    the step calls and extract a substitution for all polymorphic type from it.
    @param machine the machine which instantiate the subinstance @param ident
    the identifier of the instance which permits to find the step call @param
    submachine the machine corresponding to the subinstance @return the
    correspondance between polymorphic type id and their instantiation **)
val get_substitution: machine_t -> ident -> machine_t -> (int * Types.t) list
