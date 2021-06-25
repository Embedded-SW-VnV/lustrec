open Lustre_types

type t = { obsolete : bool; from_lusi : bool; contents : program_t }

(* extracts a header from a program representing module owner = dirname/basename *)
val extract_header: string -> string -> program_t -> top_decl list

(* read and decode a header from a file *)
val read_lusic: string -> string -> t

(* encode and write a header in a file *)
val write_lusic: bool -> program_t -> string -> string -> unit

val check_obsolete: t -> string -> unit
