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
module E = MenhirLib.ErrorReports
module L = MenhirLib.LexerUtil

(* type error =
 *   | Undefined_token of string
 *   | Unexpected_eof
 *   | Unfinished_string
 *   | Unfinished_comment
 *   | Syntax_error
 *   | String_Syntax_error of string
 *   | Unfinished_annot
 *   | Unfinished_node_spec
 *   | Annot_error of string
 *   | Node_spec_error of string *)

exception Error

(* let pp_error fmt err =
 *   match err with
 *   | Unexpected_eof ->
 *     fprintf fmt "unexpected end of file"
 *   | Undefined_token tok ->
 *     fprintf fmt "undefined token '%s'" tok
 *   | Unfinished_string ->
 *     fprintf fmt "unfinished string"
 *   | Unfinished_comment ->
 *     fprintf fmt "unfinished comment"
 *   | Syntax_error ->
 *     fprintf fmt "syntax error"
 *   | String_Syntax_error s ->
 *     fprintf fmt "syntax error in %s" s
 *   | Unfinished_annot ->
 *     fprintf fmt "unfinished annotation"
 *   | Unfinished_node_spec ->
 *     fprintf fmt "unfinished node specification"
 *   | Annot_error s ->
 *     fprintf fmt "impossible to parse the following annotation:@.%s@.@?" s
 *   | Node_spec_error s ->
 *     fprintf fmt "Impossible to parse the following node specification:@.%s@.@?" s *)

(* let report_error (loc, err) =
 *   eprintf "Syntax error: %a@."
 *     (\* pp_error err *\)
 *     Location.pp_loc loc *)

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

let reparse f start src =
  (* Allocate and initialize a lexing buffer. *)
  let lexbuf = L.init f (Lexing.from_string src) in
  (* Wrap the lexer and lexbuf together into a supplier, that is, a
     function of type [unit -> token * position * position]. *)
  let supplier = I.lexer_lexbuf_to_supplier Lexer_lustre.token lexbuf in
  (* Equip the supplier with a two-place buffer that records the positions
     of the last two tokens. This is useful when a syntax error occurs, as
     these are the token just before and just after the error. *)
  let buffer, supplier = E.wrap_supplier supplier in
  (* Fetch the parser's initial checkpoint. *)
  let checkpoint = Parser_lustre_table.Incremental.(match start with
      | Header -> header
      | Program -> prog)
      lexbuf.lex_curr_p
  in
  (* [succeed v] is invoked when the parser has succeeded and produced a
     semantic value [v]. In our setting, this cannot happen, since the
     table-based parser is invoked only when we know that there is a
     syntax error in the input file. *)
  let succeed _v = assert false in
  (* [fail checkpoint] is invoked when parser has encountered a syntax error. *)
  let fail (checkpoint : _ I.checkpoint) =
    (* Indicate where in the input file the error occurred. *)
    let location = L.range (E.last buffer) in
    (* Show the tokens just before and just after the error. *)
    let indication = sprintf "Syntax error %s.\n" (E.show (show src) buffer) in
    (* Fetch an error message from the database. *)
    let message = Parser_lustre_messages.message (state checkpoint) in
    (* Expand away the $i keywords that might appear in the message. *)
    let message = E.expand (get src checkpoint) message in
    (* Show these three components. *)
    eprintf "%s%s%s%!" location indication message;
    raise Error
  in
  (* Run the parser. *)
  (* We do not handle [Lexer.Error] because we know that we will not
     encounter a lexical error during this second parsing run. *)
  I.loop_handle succeed fail supplier checkpoint

let parse f start =
  let src, lexbuf = L.read f in
  Location.set_input f;
  let lexbuf = L.init f lexbuf in
  let parsing_fun = match start with
    | Header -> Parser_lustre.header
    | Program -> Parser_lustre.prog
  in
  try
    parsing_fun Lexer_lustre.token lexbuf
  with Parser_lustre.Error ->
    reparse f start src

(* let header parsing_fun token_fun lexbuf =
 *   try parsing_fun token_fun lexbuf with _ ->
 *     let loc = Location.curr lexbuf in
 *     let e = loc, Syntax_error in
 *     report_error e;
 *     raise (Error e)
 *
 * let prog parsing_fun token_fun lexbuf =
 *   try parsing_fun token_fun lexbuf with err ->
 *     let loc = Location.curr lexbuf in
 *     let e = loc, Syntax_error in
 *     report_error e;
 *     raise (Error e) *)


(* Local Variables: *)
(* compile-command:"make -C .." *)
(* End: *)
