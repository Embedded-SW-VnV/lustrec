open Utils

(* Clock carriers basically correspond to the "c" in "x when c" *)
type carrier_desc =
  | Carry_const of ident
  | Carry_name
  | Carry_var
  | Carry_link of carrier_expr

(* Carriers are scoped, to detect clock extrusion. In other words, we check the
   scope of a clock carrier before generalizing it. *)
and carrier_expr = {
  mutable carrier_desc : carrier_desc;
  mutable carrier_scoped : bool;
  carrier_id : int;
}

type t = { mutable cdesc : clock_desc; mutable cscoped : bool; cid : int }

(* pck stands for periodic clock. Easier not to separate pck from other
   clocks *)
and clock_desc =
  | Carrow of t * t
  | Ctuple of t list
  | Con of t * carrier_expr * ident
  | Cvar (* of clock_set *)
  (* Monomorphic clock variable *)
  | Cunivar
  (* of clock_set *)
  (* Polymorphic clock variable *)
  | Clink of t
  (* During unification, make links instead of substitutions *)
  | Ccarrying of carrier_expr * t

type error =
  | Clock_clash of t * t
  | Cannot_be_polymorphic of t
  | Invalid_imported_clock of t
  | Invalid_const of t
  | Factor_zero
  | Carrier_mismatch of carrier_expr * carrier_expr
  | Carrier_extrusion of t * carrier_expr
  | Clock_extrusion of t * t

(* Nice pretty-printing. Simplifies expressions before printing them. Non-linear
   complexity. *)
val pp : Format.formatter -> t -> unit

val pp_suffix : Format.formatter -> t -> unit

val new_var : bool -> t

val new_univar : unit -> t

val new_ck : clock_desc -> bool -> t

val new_carrier : carrier_desc -> bool -> carrier_expr

val bottom : t

val repr : t -> t

val carrier_repr : carrier_expr -> carrier_expr

val simplify : t -> t

val clock_on : t -> carrier_expr -> ident -> t

val clock_of_clock_list : t list -> t

val clock_list_of_clock : t -> t list

val root : t -> t

val branch : t -> (carrier_expr * ident) list

val common_prefix :
  (carrier_expr * ident) list ->
  (carrier_expr * ident) list ->
  (carrier_expr * ident) list

val clock_of_root_branch : t -> (carrier_expr * ident) list -> t

val split_arrow : t -> t * t

val clock_current : t -> t

val uneval : ident -> carrier_expr -> unit

val get_carrier_name : t -> carrier_expr option

val equal : t -> t -> bool

(* Disjunction relation between variables based upon their static clocks. *)
val disjoint : t -> t -> bool

val const_of_carrier : carrier_expr -> ident

val pp_error : Format.formatter -> error -> unit

exception Unify of t * t

exception Scope_carrier of carrier_expr

exception Scope_clock of t

exception Error of Location.t * error

exception Mismatch of carrier_expr * carrier_expr
