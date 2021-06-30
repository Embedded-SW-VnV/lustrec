exception Error

type start_symbol = Header | Program

module type LEXER = sig
  val token : Lexing.lexbuf -> Parser_lustre.token

  type error

  exception Error of Location.t * error

  val pp_error : Format.formatter -> error -> unit
end

module Inc : module type of Parser_lustre_table.Incremental

val parse :
  (module LEXER) ->
  ?orig_loc:Location.t ->
  Location.filename ->
  string ->
  Lexing.lexbuf ->
  ((Lexing.lexbuf -> Parser_lustre.token) -> Lexing.lexbuf -> 'a) ->
  (Lexing.position -> 'b Parser_lustre_table.MenhirInterpreter.checkpoint) ->
  'a

val parse_filename :
  (module LEXER) -> Location.filename -> start_symbol -> Lustre_types.program_t
