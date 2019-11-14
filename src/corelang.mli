(********************************************************************)
(*                                                                  *)
(*  The LustreC compiler toolset   /  The LustreC Development Team  *)
(*  Copyright 2012 -    --   ONERA - CNRS - INPT                    *)
(*                                                                  *)
(*  LustreC is free software, distributed WITHOUT ANY WARRANTY      *)
(*  under the terms of the GNU Lesser General Public License        *)
(*  version 2.1.                                                    *)
(*                                                                  *)
(********************************************************************)


open Lustre_types

exception Error of Location.t * Error.error_kind
module VSet: sig
  include Set.S
  val pp: Format.formatter -> t -> unit 
  val get: ident -> t -> elt
end with type elt = Lustre_types.var_decl 
  
val dummy_type_dec: type_dec
val dummy_clock_dec: clock_dec

val mktyp: Location.t -> type_dec_desc -> type_dec
val mkclock: Location.t -> clock_dec_desc -> clock_dec
val mkvar_decl: Location.t -> ?orig:bool ->
  ident *
    type_dec *
    clock_dec *
    bool (* is const *) *
    expr option (* value *) *
    string option (* parent id *)
  -> var_decl

val dummy_var_decl: ident -> Types.type_expr -> var_decl

val var_decl_of_const: ?parentid:ident option -> const_desc -> var_decl
val mkexpr: Location.t ->  expr_desc -> expr
val mkeq: Location.t -> ident list * expr -> eq
val mkassert: Location.t -> expr -> assert_t
val mktop_decl: Location.t -> ident -> bool -> top_decl_desc -> top_decl
val mkpredef_call: Location.t -> ident -> expr list -> expr
val mk_new_name: (ident -> bool) -> ident -> ident
val mk_new_node_name: node_desc -> ident -> ident
val mktop: top_decl_desc -> top_decl

(* constructor for machine types *)
val mkinstr: ?lustre_expr:expr -> ?lustre_eq: eq -> Machine_code_types.instr_t_desc -> Machine_code_types.instr_t
val get_instr_desc: Machine_code_types.instr_t -> Machine_code_types.instr_t_desc
val update_instr_desc: Machine_code_types.instr_t -> Machine_code_types.instr_t_desc -> Machine_code_types.instr_t
  
(*val node_table : (ident, top_decl) Hashtbl.t*)
val print_node_table:  Format.formatter -> unit -> unit
val node_name: top_decl -> ident
val node_inputs: top_decl -> var_decl list
val node_from_name: ident -> top_decl
val update_node: ident -> top_decl -> unit
val is_generic_node: top_decl -> bool
val is_imported_node: top_decl -> bool
val is_contract: top_decl -> bool
val is_node_contract: node_desc -> bool
val get_node_contract: node_desc -> contract_desc
  
val consts_table: (ident, top_decl) Hashtbl.t
val print_consts_table:  Format.formatter -> unit -> unit
val type_table: (type_dec_desc, top_decl) Hashtbl.t
val print_type_table:  Format.formatter -> unit -> unit
val is_clock_dec_type: type_dec_desc -> bool
val get_repr_type: type_dec_desc -> type_dec_desc
val is_user_type: type_dec_desc -> bool
val coretype_equal: type_dec_desc -> type_dec_desc -> bool
val tag_default: label
val tag_table: (label, top_decl) Hashtbl.t
val field_table: (label, top_decl) Hashtbl.t

val get_enum_type_tags: type_dec_desc -> label list

val get_struct_type_fields: type_dec_desc -> (label * type_dec_desc) list

val consts_of_enum_type: top_decl -> top_decl list

val const_of_bool: bool -> constant
val const_is_bool: constant -> bool
val const_negation: constant -> constant
val const_or: constant -> constant -> constant
val const_and: constant -> constant -> constant
val const_xor: constant -> constant -> constant
val const_impl: constant -> constant -> constant

val get_var: ident -> var_decl list -> var_decl
val get_node_vars: node_desc -> var_decl list
val get_node_var: ident -> node_desc -> var_decl
val get_node_eqs: node_desc -> eq list * automata_desc list
val get_node_eq: ident -> node_desc -> eq
val get_node_interface: node_desc -> imported_node_desc

(* val get_const: ident -> constant *)

val sort_handlers : (label * 'a) list -> (label * 'a) list

val is_eq_expr: expr -> expr -> bool

(* val pp_error :  Format.formatter -> error -> unit *)

(* Caution, returns an untyped, unclocked, etc, expression *)
val is_tuple_expr : expr -> bool
val ident_of_expr : expr -> ident
val expr_of_vdecl : var_decl -> expr
val expr_of_ident : ident -> Location.t -> expr
val expr_list_of_expr : expr -> expr list
val expr_of_expr_list : Location.t -> expr list -> expr
val call_of_expr: expr -> (ident * expr list * expr option)
val expr_of_dimension: Dimension.dim_expr -> expr
val dimension_of_expr: expr -> Dimension.dim_expr
val dimension_of_const: Location.t -> constant -> Dimension.dim_expr
val expr_to_eexpr: expr -> eexpr
(* REMOVED, pushed in utils.ml   val new_tag : unit -> tag *)

val add_internal_funs: unit -> unit

val pp_prog_type : Format.formatter -> program_t -> unit

val pp_prog_clock : Format.formatter -> program_t -> unit

val const_of_top: top_decl -> const_desc
val node_of_top: top_decl -> node_desc
val imported_node_of_top: top_decl -> imported_node_desc
val typedef_of_top: top_decl -> typedef_desc
val dependency_of_top: top_decl -> (bool * ident)

val get_nodes : program_t -> top_decl list
val get_imported_nodes : program_t -> top_decl list
val get_consts : program_t -> top_decl list
val get_typedefs: program_t -> top_decl list
val get_dependencies : program_t -> top_decl list
(* val prog_unfold_consts: program_t -> program_t *)

(** Returns the node named ident in the provided program. Raise Not_found *)
val get_node : ident -> program_t -> node_desc

  
val rename_static: (ident -> Dimension.dim_expr) -> type_dec_desc -> type_dec_desc
val rename_carrier: (ident -> ident) -> clock_dec_desc -> clock_dec_desc

val get_expr_vars: expr -> Utils.ISet.t
(*val expr_replace_var: (ident -> ident) -> expr -> expr*)

val eq_replace_rhs_var: (ident -> bool) -> (ident -> ident) -> eq -> eq

(** val rename_expr f_node f_var expr *)
val rename_expr : (ident -> ident) -> (ident -> ident) -> expr -> expr
(** val rename_eq f_node f_var eq *)
val rename_eq : (ident -> ident) -> (ident -> ident) -> eq -> eq
(** val rename_aut f_node f_var aut *)
val rename_aut : (ident -> ident) -> (ident -> ident) -> automata_desc -> automata_desc
(** rename_prog f_node f_var f_const prog *)
val rename_prog: (ident -> ident) -> (ident -> ident) -> (ident -> ident) -> program_t -> program_t
val rename_node: (ident -> ident) -> (ident -> ident) -> node_desc -> node_desc

val substitute_expr: var_decl list -> eq list -> expr -> expr

val copy_var_decl: var_decl -> var_decl
val copy_const: const_desc -> const_desc
val copy_node: node_desc -> node_desc
val copy_top: top_decl -> top_decl
val copy_prog: top_decl list -> top_decl list

(** Annotation expression related functions *)
val mkeexpr: Location.t ->  expr -> eexpr
val empty_contract: contract_desc
val mk_contract_var: ident -> bool -> type_dec option -> expr -> Location.t -> contract_desc
val mk_contract_guarantees: ?name:string -> eexpr -> contract_desc
val mk_contract_assume: ?name:string -> eexpr -> contract_desc
val mk_contract_mode: ident -> eexpr list -> eexpr list -> Location.t -> contract_desc
val mk_contract_import: ident -> expr -> expr -> Location.t -> contract_desc
val merge_contracts:  contract_desc -> contract_desc -> contract_desc 
val extend_eexpr: (quantifier_type * var_decl list) list -> eexpr -> eexpr
val update_expr_annot: ident -> expr -> expr_annot -> expr
(* val mkpredef_call: Location.t -> ident -> eexpr list -> eexpr*)

val expr_contains_expr: tag -> expr -> bool

val reset_cpt_fresh: unit -> unit
  
(* mk_fresh_var parentid to be registered as parent_nodeid, vars is the list of existing vars in that context *)
val mk_fresh_var: (ident * var_decl list) -> Location.t -> Types.type_expr ->  Clocks.clock_expr -> var_decl

val find_eq: ident list -> eq list -> eq * eq list

val get_expr_calls: top_decl list -> expr -> Utils.ISet.t

val eq_has_arrows: eq -> bool

val push_negations: ?neg:bool -> expr -> expr

val add_pre_expr: ident list -> expr -> expr

val mk_eq: Location.t -> expr -> expr -> expr 

(* Simple transformations: eg computation over constants *)
val partial_eval: expr -> expr

  (* Local Variables: *)
(* compile-command:"make -C .." *)
(* End: *)
