open Utils

module type BASIC_TYPES = sig
  type t

  val pp : Format.formatter -> t -> unit

  val pp_c : Format.formatter -> t -> unit

  val is_scalar_type : t -> bool

  val is_numeric_type : t -> bool

  val is_int_type : t -> bool

  val is_real_type : t -> bool

  val is_bool_type : t -> bool

  val is_dimension_type : t -> bool

  val type_int_builder : t

  val type_real_builder : t

  val type_bool_builder : t

  val type_string_builder : t

  val unify : t -> t -> unit

  val is_unifiable : t -> t -> bool
end

module type S = sig
  module BasicT : BASIC_TYPES

  type basic_type = BasicT.t

  type t = { mutable tdesc : type_desc; tid : int }

  and type_desc =
    | Tconst of ident
    (* type constant *)
    | Tbasic of basic_type
    | Tclock of t
    (* A type expression explicitely tagged as carrying a clock *)
    | Tarrow of t * t
    | Ttuple of t list
    | Tenum of ident list
    | Tstruct of (ident * t) list
    | Tarray of Dimension.t * t
    | Tstatic of Dimension.t * t
    (* a type carried by a dimension expression *)
    | Tlink of t
    (* During unification, make links instead of substitutions *)
    | Tvar
    (* Monomorphic type variable *)
    | Tunivar
  (* Polymorphic type variable *)

  type error =
    | Unbound_value of ident
    | Already_bound of ident
    | Already_defined of ident
    | Undefined_var of ISet.t
    | Declared_but_undefined of ident
    | Unbound_type of ident
    | Not_a_dimension
    | Not_a_constant
    | Assigned_constant of ident
    | WrongArity of int * int
    | WrongMorphism of int * int
    | Type_mismatch of ident
    | Type_clash of t * t
    | Poly_imported_node of ident

  exception Unify of t * t

  exception Error of Location.t * error

  val is_real_type : t -> bool

  val is_int_type : t -> bool

  val is_bool_type : t -> bool

  val is_const_type : t -> ident -> bool

  val is_static_type : t -> bool

  val is_array_type : t -> bool

  val is_dimension_type : t -> bool

  val is_address_type : t -> bool

  val is_generic_type : t -> bool

  val print_ty : Format.formatter -> t -> unit

  val repr : t -> t

  val dynamic_type : t -> t

  val type_desc : t -> type_desc

  val new_var : unit -> t

  val new_univar : unit -> t

  val new_ty : type_desc -> t

  val type_int : type_desc

  val type_real : type_desc

  val type_bool : type_desc

  val type_string : type_desc

  val array_element_type : t -> t

  val type_list_of_type : t -> t list

  val print_node_ty : Format.formatter -> t -> unit

  val get_clock_base_type : t -> t option

  val get_static_value : t -> Dimension.t option

  val is_tuple_type : t -> bool

  val type_of_type_list : t list -> t

  val split_arrow : t -> t * t

  val unclock_type : t -> t

  val bottom : t

  val map_tuple_type : (t -> t) -> t -> t

  val array_base_type : t -> t

  val array_type_dimension : t -> Dimension.t

  val pp_error : Format.formatter -> error -> unit

  val struct_field_type : t -> ident -> t

  val array_type_multi_dimension : t -> Dimension.t list
end

module Make (BasicT : BASIC_TYPES) : sig
  include S

  val print_ty_param :
    (Format.formatter -> basic_type -> unit) -> Format.formatter -> t -> unit
end
with module BasicT = BasicT

include S
