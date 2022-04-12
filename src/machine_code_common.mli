open Utils
open Lustre_types
open Machine_code_types

val pp_val : machine_t -> Format.formatter -> value_t -> unit

val find_tainter_arrow : machine_t -> var_decl -> ident option option

val is_memory : machine_t -> var_decl -> bool

val is_reset_flag : var_decl -> bool

val is_output : machine_t -> var_decl -> bool

val is_const_value : value_t -> bool

val get_const_assign : machine_t -> var_decl -> value_t

val get_stateless_status_node : node_desc -> bool * bool

val get_stateless_status : machine_t -> bool * bool

val get_stateless_status_top_decl : top_decl -> bool * bool

val is_stateless : machine_t -> bool

val mk_val : value_t_desc -> Types.t -> value_t

val vdecl_to_val : var_decl -> value_t

val vdecls_to_vals : var_decl list -> value_t list

val id_to_tag : ident -> value_t

val mk_conditional :
  ?lustre_eq:eq -> value_t -> instr_t list -> instr_t list -> instr_t

val mk_branch :
  ?lustre_eq:eq -> value_t -> (label * instr_t list) list -> instr_t

val mk_branch' :
  ?lustre_eq:eq -> var_decl -> (label * instr_t list) list -> instr_t

val mk_assign : ?lustre_eq:eq -> var_decl -> value_t -> instr_t

val empty_machine : machine_t

val arrow_machine : machine_t

val new_instance : top_decl -> tag -> ident

val value_of_dimension : machine_t -> Dimension.t -> value_t

val dimension_of_value : value_t -> Dimension.t

val pp_instr : machine_t -> Format.formatter -> instr_t -> unit

val pp_instrs : machine_t -> Format.formatter -> instr_t list -> unit

val pp_machines : Format.formatter -> machine_t list -> unit

val get_machine_opt : machine_t list -> string -> machine_t option

(* Same function but fails if no such a machine exists *)
val get_machine : machine_t list -> string -> machine_t

val get_node_def : string -> machine_t -> node_desc

val join_guards_list : instr_t list -> instr_t list

val machine_vars : machine_t -> var_decl list

module PrintSpec : sig
  val pp_spec :
    machine_t -> Format.formatter -> value_t Spec_types.formula_t -> unit
end
