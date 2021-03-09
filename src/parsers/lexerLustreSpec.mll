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

  (* open ParserLustreSpec *)
  open Parser_lustre
  open Utils

  let str_buf = Buffer.create 1024

  type error =
    (* | Undefined_token of string *)
    | Unexpected_eof
    | Unfinished_string
    | Unfinished_comment
    | Unexpected_token_annot
    | Unexpected_token_spec
    (* | Syntax_error *)
    (* | String_Syntax_error of string *)
    (* | Unfinished_annot *)
    (* | Unfinished_node_spec  *)
    (* | Annot_error of string *)
    (* | Node_spec_error of string *)

  exception Error of Location.t * error

let error lexbuf err =
  raise (Error (Location.curr lexbuf, err))

let newline token lexbuf =
  Location.Lex.newline lexbuf;
  token lexbuf

(* As advised by Caml documentation. This way a single lexer rule is
   used to handle all the possible keywords. *)
let keyword_table =
  create_hashtable 20 [
  (* "true", TRUE; *)
  (* "false", FALSE; *)
  "function", FUNCTION;
  "if", IF;
  "then", THEN;
  "else", ELSE;
  "merge", MERGE;
  "arrow", ARROW;
  "fby", FBY;
  "when", WHEN;
  "whennot", WHENNOT;
  "every", EVERY;
  "node", NODE;
  "let", LET;
  "tel", TEL;
  "returns", RETURNS;
  "var", VAR;
  "import", IMPORT;
  (* "imported", IMPORTED; *)
  "int", TINT;
  "bool", TBOOL;
  (* "float", TFLOAT; *)
  "real", TREAL;
  "clock", TCLOCK;
  "not", NOT;
  "and", AND;
  "or", OR;
  "xor", OR;
  "mod", MOD;
  "pre", PRE;
  "div", DIV;
  "const", CONST;
  (* "include", INCLUDE; *)
  "assert", ASSERT;
   "ensure", ENSURE;
  "require", REQUIRE;
  (* "observer", OBSERVER; *)
  "invariant", INVARIANT;
  "mode", MODE;
  "assume", ASSUME;
  "contract", CONTRACT;
  "guarantee", GUARANTEES;
  "exists", EXISTS;
  "forall", FORALL;
  "c_code", CCODE;
  "matlab", MATLAB;
  ]

}


let newline = ('\010' | '\013' | "\013\010")
let notnewline = [^ '\010' '\013']
let blank = [' ' '\009' '\012']

rule token = parse
  | "(*"                           { comment_line 0 lexbuf }
  | "--" notnewline* (newline|eof) { newline token lexbuf }
  | newline                        { newline token lexbuf }
  | blank +                        { token lexbuf }
  | (('-'? ['0'-'9'] ['0'-'9']* as l) '.' (['0'-'9']* as r)) as s
    {REAL (Real.create (l^r) (String.length r) s)}
  | (('-'? ['0'-'9']+ as l)  '.' (['0'-'9']+ as r) ('E'|'e') (('+'|'-') ['0'-'9'] ['0'-'9']* as exp)) as s
    {REAL (Real.create (l^r) (String.length r + -1 * int_of_string exp) s)}
  | '-'? ['0'-'9']+ 
    {INT (int_of_string (Lexing.lexeme lexbuf)) }
  (* | '/' (['_' 'A'-'Z' 'a'-'z'] ['A'-'Z' 'a'-'z' '_' '0'-'9']* '/')+ as s
       {IDENT s}
  *)
  | ['_' 'A'-'Z' 'a'-'z'] ['A'-'Z' 'a'-'z' '_' '0'-'9']*
    {let s = Lexing.lexeme lexbuf in
     try
       Hashtbl.find keyword_table s
     with Not_found ->
       IDENT s}
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
  | ';' {SCOL}
  | ':' {COL}
  | ',' {COMMA}
  | '=' {EQ}
  | '/' {DIV}
  | "&&" {AMPERAMPER}
  | "||" {BARBAR}
  | "::" {COLCOL}
  | "^" {POWER}
  | '"' { Buffer.clear str_buf; string_parse lexbuf }
  | eof { EOF }
  | _ { error lexbuf Unexpected_eof }

and comment_line n = parse
  | eof     { error lexbuf Unfinished_comment }
  | "(*"    { comment_line (n+1) lexbuf }
  | "*)"    { if n > 0 then comment_line (n-1) lexbuf else token lexbuf }
  | newline { newline (comment_line n) lexbuf }
  | _       { comment_line n lexbuf }

and string_parse = parse
  | eof         { error lexbuf Unfinished_string }
  | "\\\"" as s { Buffer.add_string str_buf s; string_parse lexbuf}
  | '"'         { STRING (Buffer.contents str_buf) }
  | _ as c      { Buffer.add_char str_buf c; string_parse lexbuf }

{

  let annot s =
    let lexbuf = Lexing.from_string s in
    try
      Parser_lustre.lustre_annot token lexbuf
    with Parser_lustre.Error ->
      error lexbuf Unexpected_token_annot

  let spec s =
    let lexbuf = Lexing.from_string s in
    try
      Parser_lustre.lustre_spec token lexbuf
    with Parser_lustre.Error ->
      error lexbuf Unexpected_token_spec
}
