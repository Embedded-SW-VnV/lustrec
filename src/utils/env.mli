open Utils

type 'a t

val initial : 'a t

val add_value : 'a t -> ident -> 'a -> 'a t

val lookup_value : 'a t -> ident -> 'a

val exists_value : 'a t -> ident -> bool

val iter : 'a t -> (ident -> 'a -> unit) -> unit

val pp : (Format.formatter -> 'a -> unit) -> Format.formatter -> 'a t -> unit

val overwrite : 'a t -> 'a t -> 'a t

val fold : (ident -> 'a -> 'b -> 'b) -> 'a t -> 'b -> 'b
