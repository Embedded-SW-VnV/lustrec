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

type t = { loc_start: Lexing.position; loc_end: Lexing.position }

type filename = string

let dummy_loc = {loc_start=Lexing.dummy_pos; loc_end=Lexing.dummy_pos}

let set_input, get_input, get_module =
  let input_name : filename ref = ref "__UNINITIALIZED__" in
  let module_name : filename ref = ref "__UNINITIALIZED__" in
  (fun name -> input_name := name; module_name := Filename.chop_extension name),
  (fun () -> !input_name),
  (fun () -> !module_name)

let curr lexbuf = {
  loc_start = lexbuf.Lexing.lex_start_p;
  loc_end = lexbuf.Lexing.lex_curr_p
}

let init lexbuf fname =
  lexbuf.Lexing.lex_curr_p <- {
    Lexing.pos_fname = fname;
    Lexing.pos_lnum = 1;
    Lexing.pos_bol = 0;
    Lexing.pos_cnum = 0;
  }

let shift_pos pos1 pos2 =
  (* Format.eprintf "Shift pos %s by pos %s@." pos1.Lexing.pos_fname pos2.Lexing.pos_fname;
   * assert (pos1.Lexing.pos_fname = pos2.Lexing.pos_fname); *)
  {Lexing.pos_fname = pos1.Lexing.pos_fname;
    Lexing.pos_lnum = pos1.Lexing.pos_lnum + pos2.Lexing.pos_lnum -1;

    (* New try *)
    Lexing.pos_bol = pos2.Lexing.pos_bol;
    Lexing.pos_cnum = pos2.Lexing.pos_cnum;
    (*
    Lexing.pos_bol = pos1.Lexing.pos_bol + pos2.Lexing.pos_bol;
    Lexing.pos_cnum =if pos2.Lexing.pos_lnum = 1 then pos1.Lexing.pos_cnum + pos2.Lexing.pos_cnum else pos2.Lexing.pos_cnum
     *)
}

    

open Format

let print loc =
  let filename = loc.loc_start.Lexing.pos_fname in
  let line = loc.loc_start.Lexing.pos_lnum in
  let start_char =
    loc.loc_start.Lexing.pos_cnum - loc.loc_start.Lexing.pos_bol
  in
  let end_char =
    loc.loc_end.Lexing.pos_cnum - loc.loc_start.Lexing.pos_cnum + start_char
  in
  let (start_char, end_char) =
    if start_char < 0 then (0,1) else (start_char, end_char)
  in
  print_string ("File \""^filename^"\", line ");
  print_int line;
  print_string ", characters ";
  print_int start_char;
  print_string "-";
  print_int end_char;
  print_string ":";
  print_newline ()

let loc_line loc = loc.loc_start.Lexing.pos_lnum 
  
let pp_loc fmt loc =
  if loc == dummy_loc then () else
  let filename = loc.loc_start.Lexing.pos_fname in
  let line = loc_line loc in
  let start_char =
    loc.loc_start.Lexing.pos_cnum - loc.loc_start.Lexing.pos_bol
  in
  let end_char =
    loc.loc_end.Lexing.pos_cnum - loc.loc_start.Lexing.pos_cnum + start_char
  in
  let (start_char, end_char) =
    if start_char < 0 then (0,1) else (start_char, end_char)
  in
  Format.fprintf fmt "File \"%s\", line %i, characters %i-%i:" filename line start_char end_char;
  (* Format.fprintf fmt "@.loc1=(%i,%i,%i) loc2=(%i,%i,%i)@."
   *   loc.loc_start.Lexing.pos_lnum
   *   loc.loc_start.Lexing.pos_bol
   *   loc.loc_start.Lexing.pos_cnum
   *   loc.loc_end.Lexing.pos_lnum
   *   loc.loc_end.Lexing.pos_bol
   *   loc.loc_end.Lexing.pos_cnum;
   *    () *)

  ()
  
let pp_c_loc fmt loc =
  let filename = loc.loc_start.Lexing.pos_fname in
  let line = loc.loc_start.Lexing.pos_lnum in
  Format.fprintf fmt "#line %i \"%s\"" line filename

let shift loc1 loc2 =
  let new_loc = 
    {loc_start = shift_pos loc1.loc_start loc2.loc_start;
     loc_end  = shift_pos loc1.loc_start loc2.loc_end
    }
  in
  (* Format.eprintf "loc1: %a@.loc2: %a@.nloc: %a@."
   *   pp_loc loc1
   *   pp_loc loc2
   *   pp_loc new_loc
   * ; *)
  new_loc

let loc_pile = ref []
let push_loc l =
  loc_pile := l::!loc_pile
let pop_loc () = loc_pile := List.tl !loc_pile
  
let symbol_rloc () =
  let curr_loc =
  {
    loc_start = Parsing.symbol_start_pos ();
    loc_end = Parsing.symbol_end_pos ()
  }
  in

  let res =
    if List.length !loc_pile > 0 then
    shift (List.hd !loc_pile) curr_loc
  else
    curr_loc
  in
  (* Format.eprintf "Loc: %a@." pp_loc res; *)
  res
    (* Local Variables: *)
    (* compile-command:"make -C .." *)
    (* End: *)
