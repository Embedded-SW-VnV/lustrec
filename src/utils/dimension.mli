open Utils

type t = { mutable dim_desc : dim_desc; dim_loc : Location.t; dim_id : int }

and dim_desc =
  | Dbool of bool
  | Dint of int
  | Dident of ident
  | Dappl of ident * t list
  | Dite of t * t * t
  | Dlink of t
  | Dvar
  | Dunivar

exception Unify of t * t

exception InvalidDimension

val mkdim : Location.t -> dim_desc -> t

val mkdim_ident : Location.t -> ident -> t

val mkdim_int : Location.t -> int -> t

val mkdim_bool : Location.t -> bool -> t

val mkdim_var : unit -> t

val mkdim_appl : Location.t -> ident -> t list -> t

val mkdim_ite : Location.t -> t -> t -> t -> t

val pp : Format.formatter -> t -> unit

val is_const : t -> bool

val is_polymorphic : t -> bool

val generalize : t -> unit

val instantiate : (int * t) list ref -> t -> t

val copy : (int * t) list ref -> t -> t

val equal : t -> t -> bool

val eval : (dim_desc list -> dim_desc) Env.t -> (ident -> t option) -> t -> unit

val unify : ?semi:bool -> t -> t -> unit

val uneval : ident -> t -> unit

val expr_replace_expr : (ident -> t) -> t -> t

val rename : (ident -> ident) -> (ident -> ident) -> t -> t

val size_const : t -> int

val check_bound : Location.t -> t -> t

val check_access : Location.t -> t -> t -> t

val multi_product : Location.t -> t list -> t
