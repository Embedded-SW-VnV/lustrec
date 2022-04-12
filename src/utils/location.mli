type t = Lexing.position * Lexing.position

type filename = string

val dummy : t

val pp : Format.formatter -> t -> unit

val pp_c : Format.formatter -> t -> unit

val get_module : unit -> filename

val curr : Lexing.lexbuf -> t

val shift : t -> t -> t

val set_input : filename -> unit

val filename_of : t -> filename

val line_of : t -> int

val start_: t -> Lexing.position
val end_: t -> Lexing.position
