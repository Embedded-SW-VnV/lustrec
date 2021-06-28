open Utils
open Format
open Lustre_types
open Machine_code_types

val rename_machine_list: ident -> var_decl list -> var_decl list
val get_machine: machine_t list -> ident -> machine_t

val full_memory_vars: ?without_arrow:bool -> machine_t list -> machine_t -> var_decl list

val rename_machine: ident -> var_decl -> var_decl
val rename_current: var_decl -> var_decl
val rename_mid: var_decl -> var_decl
val rename_next: var_decl -> var_decl
val rename_current_list: var_decl list -> var_decl list
val rename_mid_list: var_decl list -> var_decl list
val rename_next_list: var_decl list -> var_decl list

val concat: string -> ident -> ident

val arrow_vars: machine_t list -> machine_t -> var_decl list
val reset_vars: machine_t list -> machine_t -> var_decl list
val step_vars: machine_t list -> machine_t -> var_decl list
val step_vars_m_x: machine_t list -> machine_t -> var_decl list
val local_memory_vars: machine_t -> var_decl list
val inout_vars: machine_t -> var_decl list

val pp_type: formatter -> Types.t -> unit
val pp_machine_reset_name: formatter -> ident -> unit
val pp_machine_step_name: formatter -> ident -> unit
val pp_machine_stateless_name: formatter -> ident -> unit
val pp_conj: (formatter -> 'a -> unit) -> formatter -> 'a list -> unit
val pp_decl_var: formatter -> var_decl -> unit

val registered_keywords: ident list

val protect_kwd: ident -> ident
