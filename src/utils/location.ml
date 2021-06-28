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

open Lexing
module Lex = MenhirLib.LexerUtil

type t = position * position

type filename = string

let dummy = dummy_pos, dummy_pos

let set_input, get_input, get_module =
  let input_name : filename ref = ref "__UNINITIALIZED__" in
  let module_name : filename ref = ref "__UNINITIALIZED__" in
  ( (fun name ->
      input_name := name;
      module_name := Filename.chop_extension name),
    (fun () -> !input_name),
    fun () -> !module_name )

let curr lexbuf = lexbuf.lex_start_p, lexbuf.lex_curr_p

let filename_of_loc (s, _) = s.pos_fname

let filename_of_lexbuf lexbuf = lexbuf.lex_start_p.pos_fname

let shift_pos pos1 pos2 =
  (* Format.eprintf "Shift pos %s by pos %s@." pos1.Lexing.pos_fname pos2.Lexing.pos_fname;
   * assert (pos1.Lexing.pos_fname = pos2.Lexing.pos_fname); *)
  {
    pos_fname = pos1.pos_fname;
    pos_lnum = pos1.pos_lnum + pos2.pos_lnum - 1;
    (* New try *)
    (* pos_bol = pos2.pos_bol; *)
    pos_bol = pos1.pos_bol + pos2.pos_bol;
    pos_cnum =
      pos1.pos_cnum + pos2.pos_cnum
      (* pos_cnum = pos2.pos_cnum; *)
      (* pos_bol = pos1.pos_bol + pos2.pos_bol; pos_cnum =if pos2.pos_lnum = 1
         then pos1.pos_cnum + pos2.pos_cnum else pos2.pos_cnum *);
  }

let loc_line (s, _e) = s.pos_lnum

let pp fmt loc =
  if loc = dummy then () else Format.fprintf fmt "%s" (Lex.range loc)

let pp_c fmt (s, _e) =
  let filename = s.pos_fname in
  let line = s.pos_lnum in
  Format.fprintf fmt "#line %i \"%s\"" line filename

let shift (_s1, e1) (s2, e2) = shift_pos e1 s2, shift_pos e1 e2

(* Local Variables: *)
(* compile-command:"make -C .." *)
(* End: *)
