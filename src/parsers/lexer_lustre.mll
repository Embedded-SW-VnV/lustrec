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

{
open Parser_lustre
open Utils

module Lex = MenhirLib.LexerUtil

(* As advised by Caml documentation. This way a single lexer rule is
   used to handle all the possible keywords. *)
let keyword_table =
  create_hashtable 20 [
  "function", FUNCTION;
  "struct", STRUCT;
  "enum", ENUM;
  "automaton", AUTOMATON;
  "state", STATE;
  "until", UNTIL;
  "unless", UNLESS;
  "resume", RESUME;
  "restart", RESTART;
  "if", IF;
  "then", THEN;
  "else", ELSE;
  "merge", MERGE;
  "arrow", ARROW;
  "fby", FBY;
  "when", WHEN;
  "whenot", WHENNOT;
  "every", EVERY;
  "node", NODE;
  "let", LET;
  "tel", TEL;
  "returns", RETURNS;
  "var", VAR;
  (* "imported", IMPORTED; *)
  "import", IMPORT;
  "type", TYPE;
  "int", TINT;
  "bool", TBOOL;
  (* "float", TFLOAT; *)
  "real", TREAL;
  "clock", TCLOCK;
  "not", NOT;
  "true", TRUE;
  "false", FALSE;
  "and", AND;
  "or", OR;
  "xor", XOR;
  "mod", MOD;
  "pre", PRE;
  "div", DIV;
  "const", CONST;
  "assert", ASSERT;
  "contract", CONTRACT;
  "lib", LIB;
  "prototype", PROTOTYPE;
  "ensure", ENSURE;
  "require", REQUIRE;
  (* "observer", OBSERVER; *)
  "invariant", INVARIANT;
  "mode", MODE;
  "assume", ASSUME;
  "guarantee", GUARANTEES;
  "exists", EXISTS;
  "forall", FORALL;
 
  "c_code", CCODE; (* not sure how it is used *)
  "matlab", MATLAB; (* same as above *)
]


(* Buffer for parsing specification/annotation *)
let buf = Buffer.create 1024

  type error =
    | Undefined_token of string
    | Unfinished_comment
    | Unfinished_annot
    | Unfinished_node_spec
    | Annot_error of string
    | Node_spec_error of string

  exception Error of Location.t * error

let pp_error fmt =
  let open Format in
  function
  | Undefined_token s ->
    fprintf fmt "Undefined token '%s'." s
  | Unfinished_comment ->
    fprintf fmt "Unfinished comment."
  | Unfinished_annot ->
    fprintf fmt "Unfinished annotation."
  | Unfinished_node_spec ->
    fprintf fmt "Unfinished node specification."
  | Annot_error s ->
    fprintf fmt "Ill-formed annotation '%s'." s
  | Node_spec_error s ->
    fprintf fmt "Ill-formed node specification '%s'." s

let error_with loc err =
  raise (Error (loc, err))

let error lexbuf =
  error_with (Location.curr lexbuf)

let newline token lexbuf =
  Lex.newline lexbuf;
  token lexbuf

let make_annot orig_loc s =
  let lexbuf = Lexing.from_string s in
  let f = Location.filename_of_loc orig_loc in
  ANNOT (Parse.parse (module LexerLustreSpec) ~orig_loc f s lexbuf
        Parser_lustre.lustre_annot Parse.Inc.lustre_annot)

let make_spec orig_loc s =
  let lexbuf = Lexing.from_string s in
  let f = Location.filename_of_loc orig_loc in
  NODESPEC (Parse.parse (module LexerLustreSpec) ~orig_loc f s lexbuf
        Parser_lustre.lustre_spec Parse.Inc.lustre_spec)
}

let newline = ('\010' | '\013' | "\013\010")
let notnewline = [^ '\010' '\013']
let blank = [' ' '\009' '\012']

rule token = parse
| "--@" { Buffer.clear buf;
          let loc = Location.curr lexbuf in
          extra_singleline (make_spec loc) lexbuf }
| "(*@" { Buffer.clear buf; 
          let loc = Location.curr lexbuf in
          extra_multiline (make_spec loc) Unfinished_node_spec 0 lexbuf }
| "--!" { Buffer.clear buf;
          let loc = Location.curr lexbuf in
          extra_singleline (make_annot loc) lexbuf }
| "(*!" { Buffer.clear buf;
          let loc = Location.curr lexbuf in
          extra_multiline (make_annot loc) Unfinished_annot 0 lexbuf }
| "(*"  { comment 0 lexbuf }
| "--" [^ '!' '@'] notnewline* (newline|eof)
    { newline token lexbuf }
| newline { newline token lexbuf }
| blank + { token lexbuf }
| ((['0'-'9']+ as l)  '.' (['0'-'9']* as r) ('E'|'e') (('+'|'-')? ['0'-'9']+ as exp)) as s
    {REAL (Real.create (l^r) (String.length r + -1 * int_of_string exp) s)}
| ((['0'-'9']+ as l) '.' (['0'-'9']* as r)) as s
    {REAL (Real.create (l^r) (String.length r) s)}
| ['0'-'9']+ 
    {INT (int_of_string (Lexing.lexeme lexbuf)) }
| "tel." {TEL}
| "tel;" {TEL}
| "#open" { OPEN }
| "include" { INCLUDE }
| ['_' 'a'-'z'] [ '_' 'a'-'z' 'A'-'Z' '0'-'9']* as s
    { try Hashtbl.find keyword_table s with Not_found -> IDENT s }
| ['A'-'Z'] [ '_' 'a'-'z' 'A'-'Z' '0'-'9']* as s
    { try Hashtbl.find keyword_table s with Not_found -> UIDENT s }
| "->" {ARROW}
| "=>" {IMPL}
| "<=" {LTE}
| ">=" {GTE}
| "<>" {NEQ}
| '<' {LT}
| '>' {GT}
| "!=" {NEQ}
| '-' {MINUS}
| '+' {PLUS}
| '/' {DIV}
| '*' {MULT}
| '=' {EQ}
| '(' {LPAR}
| ')' {RPAR}
| '[' {LBRACKET}
| ']' {RBRACKET}
| '{' {LCUR}
| '}' {RCUR}
| ';' {SCOL}
| ':' {COL}
| ',' {COMMA}
| '=' {EQ}
| "&&" {AMPERAMPER}
| "||" {BARBAR}
| "::" {COLCOL}
| "^" {POWER}
| '"' {QUOTE}
| '.' {POINT}
| eof { EOF }
| _ { error lexbuf (Undefined_token (Lexing.lexeme lexbuf)) }

and comment n = parse
  | eof     { error lexbuf Unfinished_comment }
  | "(*"    { comment (n+1) lexbuf }
  | "*)"    { if n > 0 then comment (n-1) lexbuf else token lexbuf }
  | newline { newline (comment n) lexbuf }
  | _       { comment n lexbuf }

and extra_singleline extra = parse
  | eof     { extra (Buffer.contents buf) }
  | newline { newline (fun _ -> extra (Buffer.contents buf)) lexbuf }
  | _ as c  { Buffer.add_char buf c; extra_singleline extra lexbuf }

and extra_multiline extra err n = parse
  | eof          { error lexbuf err }
  | "*)" as s    { if n > 0 then begin
                     Buffer.add_string buf s;
                     extra_multiline extra err (n-1) lexbuf
                   end else
                     extra (Buffer.contents buf) }
  | "(*" as s    { Buffer.add_string buf s;
                   extra_multiline extra err (n+1) lexbuf }
  | newline as s { newline (fun lexbuf ->
                     Buffer.add_string buf s;
                     extra_multiline extra err n lexbuf) lexbuf }
  | _ as c       { Buffer.add_char buf c; extra_multiline extra err n lexbuf }

(* and annot_singleline loc = parse
 *   | eof     { make_annot loc (Buffer.contents buf) }
 *   | newline { newline (fun _ -> make_annot loc (Buffer.contents buf)) lexbuf }
 *   | _ as c  { Buffer.add_char buf c; annot_singleline loc lexbuf }
 *
 * and annot_multiline loc n = parse
 *   | eof          { error lexbuf Unfinished_annot }
 *   | "*\)" as s    { if n > 0 then
 *                      (Buffer.add_string buf s; annot_multiline (n-1) lexbuf)
 *                    else
 *                      make_annot (Buffer.contents buf) lexbuf }
 *   | "(\*" as s    { Buffer.add_string buf s; annot_multiline (n+1) lexbuf }
 *   | newline as s { newline (fun lexbuf ->
 *         Buffer.add_string buf s; annot_multiline n lexbuf) lexbuf }
 *   | _ as c       { Buffer.add_char buf c; annot_multiline n lexbuf }
 *
 * and spec_singleline loc = parse
 *   | eof     { make_spec loc (Buffer.contents buf) }
 *   | newline { newline (fun _ -> make_spec loc (Buffer.contents buf)) lexbuf }
 *   | _ as c  { Buffer.add_char buf c; spec_singleline loc lexbuf }
 *
 * and spec_multiline loc n = parse
 *   | eof          { error lexbuf Unfinished_node_spec }
 *   | "*\)" as s    { if n > 0 then
 *                      (Buffer.add_string buf s; spec_multiline loc (n-1) lexbuf)
 *                    else
 *                      make_spec loc (Buffer.contents buf) }
 *   | "(\*" as s    { Buffer.add_string buf s; spec_multiline loc (n+1) lexbuf }
 *   | newline as s { newline (fun lexbuf ->
 *         Buffer.add_string buf s; spec_multiline loc n lexbuf) lexbuf }
 *   | _ as c       { Buffer.add_char buf c; spec_multiline loc n lexbuf } *)
