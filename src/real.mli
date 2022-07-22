type t
val pp: Format.formatter -> t -> unit
val pp_ada: Format.formatter -> t -> unit
val create: string -> int -> string -> t
(*val create_num: Num.num -> string -> t*)
val create_q: Q.t -> string -> t

val add: t -> t -> t
val minus: t -> t -> t
val times: t -> t -> t
val div: t -> t -> t
val uminus: t -> t

val lt: t -> t -> bool
val le: t -> t -> bool
val gt: t -> t -> bool
val ge: t -> t -> bool
val eq: t -> t -> bool
val diseq: t -> t -> bool
  
(*val to_num: t -> Num.num*)
val to_q: t -> Q.t
val to_string: t -> string
val eq: t -> t -> bool
val zero: t

val is_zero: t -> bool
val is_one: t -> bool
