open Utils

val pp_file_decl: Format.formatter -> ident -> int -> unit
val pp_file_open: Format.formatter -> ident -> int -> string
val pp_put_var: Format.formatter -> string -> ident -> Types.t -> ident -> unit
