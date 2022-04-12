open Format

type printer = formatter -> unit

val pp_str : string -> printer

val pp_filename : string -> formatter -> printer -> unit
(** Print a filename by lowercasing the base and appending an extension. @param
    extension the extension to append to the package name @param fmt the
    formatter @param pp_name the file base name printer **)
