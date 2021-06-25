val core_dependency: string -> string
val plugin_opt: string * (unit -> unit) * (Format.formatter -> unit) *
                (string * Arg.spec * string) list -> (string * Arg.spec * string) list

val name_dependency: ('a * string) -> string -> string
val get_witness_dir: string -> string
