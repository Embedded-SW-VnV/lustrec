type options_spec = (string * Arg.spec * string) list

val core_dependency: string -> string
val plugin_opt: string * (unit -> unit) * (Format.formatter -> unit) *
                options_spec -> options_spec

val name_dependency: ('a * string) -> string -> string
val get_witness_dir: string -> string

val verifier_opt: string * (unit -> unit) * options_spec -> options_spec

val lustrec_options: options_spec

val lustrev_options: options_spec

val lustret_options: options_spec

val setup: unit -> unit
