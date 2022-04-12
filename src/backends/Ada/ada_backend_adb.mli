open Utils
open Machine_code_types

val pp_file :
  Format.formatter ->
  (ident * ((tag * Types.t) list * machine_t)) list
  * ((machine_t option * ident list) * machine_t) ->
  unit
(** Print the package definition(ads) of a machine. It requires the list of all
    typed instance. A typed submachine instance is (ident, type_machine) with
    ident the instance name and typed_machine is (substitution, machine) with
    machine the machine associated to the instance and substitution the
    instanciation of all its polymorphic types. @param fmt the formater to print
    on @param typed_submachines list of all typed machine instances of this
    machine @param m the machine **)
