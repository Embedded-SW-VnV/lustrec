open Format

open Machine_code_types
open Lustre_types
open Types

open Ada_printer
open Misc_printer

val pp_state_name : printer
val pp_state_type : printer
val pp_reset_procedure_name : printer
val pp_step_procedure_name : printer
val pp_main_procedure_name : printer
val pp_polymorphic_type : int -> printer

val is_builtin_fun : string -> bool
val ada_supported_funs : (string*(string*string)) list

val pp_var_name : var_decl -> formatter -> unit
val pp_var : ((string*printer) list) -> formatter -> var_decl -> unit
val pp_value : ((string*printer) list) -> formatter -> value_t -> unit
val pp_type : formatter -> type_expr -> unit
val pp_var_type : formatter -> var_decl -> unit

val pp_package_name : machine_t -> printer
val pp_package_name_with_polymorphic : (int * Types.type_expr) list -> machine_t -> printer

val mk_default_value : type_expr -> value_t

val build_pp_var_decl : parameter_mode -> ada_with -> var_decl -> ada_var_decl
val build_pp_var_decl_local : ada_with -> var_decl -> ada_local_decl
val build_pp_var_decl_step_input : parameter_mode -> ada_with -> machine_t -> (ada_var_decl list list)
val build_pp_var_decl_step_output : parameter_mode -> ada_with -> machine_t -> (ada_var_decl list list)
val build_pp_arg_step : machine_t -> (ada_var_decl list list)
val build_pp_arg_reset : machine_t -> (ada_var_decl list list)
val build_pp_state_decl_from_subinstance : parameter_mode -> ada_with -> (string * ((int * Types.type_expr) list * Machine_code_types.machine_t)) -> ada_var_decl

val pp_machine_filename : string -> formatter -> machine_t -> unit
val pp_main_filename : formatter -> machine_t -> unit
