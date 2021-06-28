open Utils
open Format
open Machine_code_types

(** Print the main file calling in a loop the step function of the main
    machine. @param fmt the formater to print on @param machine the main
    machine **)
val pp_main_adb: formatter -> machine_t -> unit

(** Print the name of the ada project file. @param base_name name of the
    lustre file @param fmt the formater to print on **)
val pp_project_name: string -> formatter -> unit

(** Print the gpr project file, if there is a machine in machine_opt then an
    executable project is made else it is a library. @param fmt the formater
    to print on @param machine_opt the main machine option **)
val pp_project_file: machine_t list -> string -> formatter -> machine_t option -> unit

(** Print the name of the ada project configuration file. @param fmt the
    formater to print on @param main_machine the machine associated to the
    main node **)
val pp_project_configuration_name: formatter -> string -> unit

(** Print the project configuration file. @param fmt the formater to print on
    **)
val pp_project_configuration_file: formatter -> unit
