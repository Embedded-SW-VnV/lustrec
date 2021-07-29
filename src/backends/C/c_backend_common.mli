open Utils
open Format
open Lustre_types
open Machine_code_types

val pp_file_decl : formatter -> ident -> int -> unit

val pp_file_open : formatter -> ident -> int -> string

val pp_put_var : formatter -> string -> ident -> Types.t -> ident -> unit

val pp_ptr : formatter -> ident -> unit

val pp_machine_set_reset_name : formatter -> ident -> unit

val pp_machine_clear_reset_name : formatter -> ident -> unit

val pp_machine_init_name : formatter -> ident -> unit

val pp_machine_clear_name : formatter -> ident -> unit

val pp_machine_step_name : formatter -> ident -> unit

val pp_machine_alloc_name : formatter -> ident -> unit

val pp_machine_static_alloc_name : ?ghost:bool -> formatter -> ident -> unit

val pp_machine_dealloc_name : formatter -> ident -> unit

val pp_global_init_name : formatter -> ident -> unit

val pp_global_clear_name : formatter -> ident -> unit

val pp_machine_static_declare_name : ?ghost:bool -> formatter -> ident -> unit

val pp_machine_static_link_name : ?ghost:bool -> formatter -> ident -> unit

val pp_global_init_prototype : formatter -> ident -> unit

val pp_global_clear_prototype : formatter -> ident -> unit

val pp_alloc_prototype : formatter -> ident * var_decl list -> unit

val pp_dealloc_prototype : formatter -> ident -> unit

val pp_import_prototype : formatter -> dep_t -> unit

val pp_import_alloc_prototype : formatter -> dep_t -> unit

val pp_c_var_read :
  ?test_output:bool -> machine_t -> formatter -> var_decl -> unit

val pp_c_var_write : machine_t -> formatter -> var_decl -> unit

val pp_c_var :
  machine_t ->
  ident ->
  (formatter -> var_decl -> unit) ->
  formatter ->
  var_decl ->
  unit

val pp_c_dimension : formatter -> Dimension.t -> unit

val pp_label : formatter -> label -> unit

val pp_c_tag : formatter -> label -> unit

val pp_reset_assign : ident -> formatter -> bool -> unit

val pp_assign :
  machine_t ->
  ident ->
  (formatter -> var_decl -> unit) ->
  formatter ->
  var_decl * value_t ->
  unit

val pp_c_type :
  ?var_is_contract:bool ->
  ?pp_c_basic_type_desc:(Types.t -> string) ->
  ?var_opt:var_decl ->
  ident ->
  formatter ->
  Types.t ->
  unit

val pp_basic_c_type :
  ?pp_c_basic_type_desc:(Types.t -> string) ->
  ?var_opt:var_decl ->
  formatter ->
  Types.t ->
  unit

val pp_machine_memtype_name : ?ghost:bool -> formatter -> ident -> unit

val pp_array_suffix : formatter -> ident list -> unit

val pp_print_version : formatter -> unit -> unit

val pp_machine_struct : ?ghost:bool -> formatter -> machine_t -> unit

val pp_reset_flag :
  ?indirect:bool -> (formatter -> 'a -> unit) -> formatter -> 'a -> unit

val pp_reset_flag' : ?indirect:bool -> formatter -> ident -> unit

val pp_machine_decl :
  ?ghost:bool -> (formatter -> 'a -> unit) -> formatter -> ident * 'a -> unit

val pp_machine_decl' : ?ghost:bool -> formatter -> ident * ident -> unit

val pp_file : ident -> formatter -> ident * ident -> unit

val pp_basic_lib_fun :
  bool -> ident -> (formatter -> 'a -> unit) -> formatter -> 'a list -> unit

val pp_c_decl_input_var : formatter -> var_decl -> unit

(* Prints a value expression [v], with internal function calls only. [pp_var] is
   a printer for variables (typically [pp_c_var_read]), but an offset suffix may
   be added for array variables *)
val pp_c_val :
  machine_t ->
  ident ->
  (formatter -> var_decl -> unit) ->
  formatter ->
  value_t ->
  unit

(* Prints a constant value *)
val pp_c_const : formatter -> constant -> unit

(* Declaration of a local/mem variable: - if it's an array/matrix/etc, its
   size(s) should be known in order to statically allocate memory, so we print
   the full type *)
val pp_c_decl_local_var :
  ?pp_c_basic_type_desc:(Types.t -> string) ->
  machine_t ->
  formatter ->
  var_decl ->
  unit

(* type directed initialization: useless wrt the lustre compilation model,
   except for MPFR injection, where values are dynamically allocated *)
val pp_initialize :
  machine_t ->
  ident ->
  (formatter -> var_decl -> unit) ->
  formatter ->
  var_decl ->
  unit

(* type directed clear: useless wrt the lustre compilation model, except for
   MPFR injection, where values are dynamically allocated *)
val pp_clear :
  machine_t ->
  ident ->
  (formatter -> var_decl -> unit) ->
  formatter ->
  var_decl ->
  unit

val pp_static_declare_macro :
  ?ghost:bool -> formatter -> machine_t * ident * ident -> unit

val pp_static_link_macro :
  ?ghost:bool -> formatter -> machine_t * ident * ident -> unit

val pp_static_alloc_macro :
  ?ghost:bool -> formatter -> machine_t * ident * ident -> unit

val mk_call_var_decl : Location.t -> ident -> var_decl

val pp_c_basic_type_desc : Types.t -> string

val has_c_prototype : ident -> dep_t list -> bool

val reset_label : label

type loop_index = LVar of ident | LInt of int ref | LAcc of value_t

val mk_loop_var : machine_t -> unit -> ident

(* Computes the list of nested loop variables together with their dimension
   bounds.
 *  - LInt r stands for loop expansion (no loop variable, but int loop
      index)
 *  - LVar v stands for loop variable v *)
val mk_loop_variables :
  machine_t -> Types.t -> int -> (Dimension.t * loop_index) list

val reset_loop_counter : unit -> unit

val reorder_loop_variables :
  (Dimension.t * loop_index) list -> (Dimension.t * loop_index) list

(* Prints a [value] of type [var_type] indexed by the suffix list [loop_vars] *)
val pp_value_suffix :
  ?indirect:bool ->
  machine_t ->
  ident ->
  Types.t ->
  (Dimension.t * loop_index) list ->
  (formatter -> var_decl -> unit) ->
  formatter ->
  value_t ->
  unit

(* Generation of a non-clashing name for the self memory variable (for step and
   reset functions) *)
val mk_self : machine_t -> ident

val mk_mem : machine_t -> ident

val mk_mem_in : machine_t -> ident

val mk_mem_out : machine_t -> ident

val mk_mem_reset : machine_t -> ident

(* Generation of a non-clashing name for the attribute variable of static
   allocation macro *)
val mk_attribute : machine_t -> ident

(* Generation of a non-clashing name for the instance variable of static
   allocation macro *)
val mk_instance : machine_t -> ident

val mpfr_vars : var_decl list -> var_decl list

val mpfr_consts : const_desc list -> const_desc list

val reset_flag_name : string

val file_to_module_name : string -> string

val protect_filename : string -> string

(* Computes the depth to which multi-dimension array assignments should be
   expanded. It equals the maximum number of nested static array constructions
   accessible from root [v]. *)
val expansion_depth : value_t -> int

module type MODIFIERS_GHOST_PROTO = sig
  val pp_ghost_parameters :
    ?cut:bool ->
    formatter ->
    (string * (formatter -> string -> unit)) list ->
    unit
end

module EmptyGhostProto : MODIFIERS_GHOST_PROTO

module Protos (Mod : MODIFIERS_GHOST_PROTO) : sig
  val pp_stateless_prototype :
    formatter -> ident * var_decl list * var_decl list -> unit

  val pp_clear_reset_prototype :
    ident -> ident -> formatter -> ident * var_decl list -> unit

  val pp_set_reset_prototype :
    ident -> ident -> formatter -> ident * var_decl list -> unit

  val pp_step_prototype :
    ident -> ident -> formatter -> ident * var_decl list * var_decl list -> unit

  val pp_init_prototype : ident -> formatter -> ident * var_decl list -> unit

  val pp_clear_prototype : ident -> formatter -> ident * var_decl list -> unit
end
