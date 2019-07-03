open Format

type printer = formatter -> unit

(** Encapsulate a pretty print function to lower case its result when applied
   @param pp the pretty print function
   @param fmt the formatter
   @param arg the argument of the pp function
**)
let pp_lowercase pp fmt =
  let str = asprintf "%t" pp in
  fprintf fmt "%s" (String. lowercase_ascii str)

(** Print a filename by lowercasing the base and appending an extension.
   @param extension the extension to append to the package name
   @param fmt the formatter
   @param pp_name the file base name printer
**)
let pp_filename extension fmt pp_name =
  fprintf fmt "%t.%s"
    (pp_lowercase pp_name)
    extension

let pp_str str fmt = fprintf fmt "%s" str
