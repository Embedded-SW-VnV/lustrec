open Utils
(* open Types *)

module Make (T : Types.S) : sig
  (* see https://stackoverflow.com/a/37307124 *)
  include module type of struct
    include T
  end

  val type_int : t

  val type_real : t

  val type_bool : t

  val type_string : t

  val type_clock : t -> t

  val type_const : ident -> t

  val type_enum : ident list -> t

  val type_struct : (ident * t) list -> t

  val type_arrow : t -> t -> t

  val type_array : Dimension.t -> t -> t

  val type_static : Dimension.t -> t -> t
end

(* include Types.S *)
val type_int : Types.t

val type_bool : Types.t

val type_real : Types.t

val type_const : ident -> Types.t

val type_static : Dimension.t -> Types.t -> Types.t

val type_bin_poly_op : Types.t

val type_unary_poly_op : Types.t

val type_bin_int_op : Types.t

val type_bin_bool_op : Types.t

val type_bin_comp_op : Types.t

val type_unary_bool_op : Types.t

val type_tuple : Types.t list -> Types.t

val type_arrow : Types.t -> Types.t -> Types.t

val type_array : Dimension.t -> Types.t -> Types.t
