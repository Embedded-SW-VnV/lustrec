(********************************************************************)
(*                                                                  *)
(*  The LustreC compiler toolset   /  The LustreC Development Team  *)
(*  Copyright 2012 -    --   ONERA - CNRS - INPT                    *)
(*                                                                  *)
(*  LustreC is free software, distributed WITHOUT ANY WARRANTY      *)
(*  under the terms of the GNU Lesser General Public License        *)
(*  version 2.1.                                                    *)
(*                                                                  *)
(********************************************************************)
open Utils.Format

module I = Parser_lustre_table.MenhirInterpreter
module Inc = Parser_lustre_table.Incremental
module E = MenhirLib.ErrorReports
module L = MenhirLib.LexerUtil

exception Error

type start_symbol =
  | Header
  | Program

(* [env checkpoint] extracts a parser environment out of a checkpoint,
   which must be of the form [HandlingError env]. *)
let env checkpoint =
  match checkpoint with
  | I.HandlingError env -> env
  | _ -> assert false

(* [state checkpoint] extracts the number of the current state out of a
   checkpoint. *)
let state checkpoint : int =
  match I.top (env checkpoint) with
  | Some (I.Element (s, _, _, _)) ->
    I.number s
  | None ->
    (* Hmm... The parser is in its initial state. The incremental API
       currently lacks a way of finding out the number of the initial
       state. It is usually 0, so we return 0. This is unsatisfactory
       and should be fixed in the future. *)
      0

(* [show text (pos1, pos2)] displays a range of the input text [text]
   delimited by the positions [pos1] and [pos2]. *)
let show text positions =
  E.extract text positions
  |> E.sanitize
  |> E.compress
  |> E.shorten 20 (* max width 43 *)

(* [get text checkpoint i] extracts and shows the range of the input text that
   corresponds to the [i]-th stack cell. The top stack cell is numbered zero. *)
let get text checkpoint i =
  match I.get i (env checkpoint) with
  | Some (I.Element (_, _, pos1, pos2)) ->
    show text (pos1, pos2)
  | None ->
    (* The index is out of range. This should not happen if [$i]
       keywords are correctly inside the syntax error message
       database. The integer [i] should always be a valid offset
       into the known suffix of the stack. *)
    "???"

module type LEXER = sig
  val token: Lexing.lexbuf -> Parser_lustre.token
  type error
  exception Error of Location.t * error
  val pp_error: formatter -> error -> unit
end

let reparse (module Lexer : LEXER) ?orig_loc filename start src =
  (* Allocate and initialize a lexing buffer. *)
  let lexbuf = L.init filename (Lexing.from_string src) in
  (* Wrap the lexer and lexbuf together into a supplier, that is, a
     function of type [unit -> token * position * position]. *)
  let supplier = I.lexer_lexbuf_to_supplier Lexer.token lexbuf in
  (* Equip the supplier with a two-place buffer that records the positions
     of the last two tokens. This is useful when a syntax error occurs, as
     these are the token just before and just after the error. *)
  let buffer, supplier = E.wrap_supplier supplier in
  (* Fetch the parser's initial checkpoint. *)
  let checkpoint = start lexbuf.lex_curr_p in
  (* [succeed v] is invoked when the parser has succeeded and produced a
     semantic value [v]. In our setting, this cannot happen, since the
     table-based parser is invoked only when we know that there is a
     syntax error in the input file. *)
  let succeed _v = assert false in
  (* [fail checkpoint] is invoked when parser has encountered a syntax error. *)
  let fail (checkpoint : _ I.checkpoint) =
    (* Indicate where in the input file the error occurred. *)
    let loc = E.last buffer in
    let loc = match orig_loc with Some loc' -> Location.shift loc' loc | _ -> loc in
    (* Show the tokens just before and just after the error. *)
    let indication = E.show (show src) buffer in
    (* Fetch an error message from the database. *)
    let message = Parser_lustre_messages.message (state checkpoint) in
    (* Expand away the $i keywords that might appear in the message. *)
    let message = E.expand (get src checkpoint) message in
    (* Show these three components. *)
    eprintf "@[<v>%aSyntax error %s.@,%s@]@."
      Location.pp_loc loc indication message;
    raise Error
  in
  (* Run the parser. *)
  (* We do not handle [Lexer.Error] because we know that we will not
     encounter a lexical error during this second parsing run. *)
  I.loop_handle succeed fail supplier checkpoint

let parse (module Lexer : LEXER) ?orig_loc filename src lexbuf start_mono start_incr =
  let lexbuf = L.init filename lexbuf in
  try
    start_mono Lexer.token lexbuf
  with
  | Lexer.Error (loc, err) ->
    let loc = match orig_loc with Some loc' -> Location.shift loc' loc | _ -> loc in
    eprintf "@[<v>%aSyntax error.@,%a@]@."
      Location.pp_loc loc Lexer.pp_error err;
    raise Error
  | Parser_lustre.Error ->
    reparse (module Lexer) ?orig_loc filename start_incr src

let parse_filename (module Lexer : LEXER) filename start =
  let start_mono, start_incr = match start with
    | Header -> Parser_lustre.header, Inc.header
    | Program -> Parser_lustre.prog, Inc.prog
  in
  let src, lexbuf = L.read filename in
  Location.set_input filename;
  parse (module Lexer) filename src lexbuf start_mono start_incr

(* Local Variables: *)
(* compile-command:"make -C .." *)
(* End: *)
