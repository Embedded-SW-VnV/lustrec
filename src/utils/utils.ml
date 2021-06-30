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

open Graph

(* XXX: UNUSED *)
(* type rat = int * int *)

type ident = string

type tag = int

(* XXX: UNUSED *)
(* type longident = (string * tag) list *)

exception TransposeError of int * int

(** General utility functions. *)
let create_hashtable size init =
  let tbl = Hashtbl.create size in
  List.iter (fun (key, data) -> Hashtbl.add tbl key data) init;
  tbl

module IdentModule = struct
  (* Node module *)
  type t = ident

  let compare = compare

  let hash n = Hashtbl.hash n

  let equal n1 n2 = n1 = n2
end

module IMap = struct
  include Map.Make (IdentModule)

  let diff m1 m2 =
    merge
      (fun _ o1 o2 ->
        match o1, o2 with
        | Some v1, Some v2 ->
          if v1 = v2 then None else o1
        | _ ->
          o1)
      m1
      m2

  let of_list l = List.fold_left (fun m (x, v) -> add x v m) empty l

  let pp ?(comment = "") pp_val fmt m =
    Format.fprintf fmt "@[<hv 0>@[<hv 2>{ %s" comment;
    iter (fun key v -> Format.fprintf fmt "@ %s -> %a" key pp_val v) m;
    Format.fprintf fmt "@]@ }@]"
end

module ISet = struct
  include Set.Make (IdentModule)

  let pp fmt t =
    let open Format in
    fprintf fmt "@[<hv 0>@[<hv 2>{";
    iter (fun s -> fprintf fmt "@ %s" s) t;
    fprintf fmt "@]@ }@]"
end

module IdentDepGraph = Imperative.Digraph.ConcreteBidirectional (IdentModule)
module TopologicalDepGraph = Topological.Make (IdentDepGraph)
module ComponentsDepGraph = Components.Make (IdentDepGraph)

(*module DotGraph = Graphviz.Dot (IdentDepGraph)*)
module Bfs = Traverse.Bfs (IdentDepGraph)

exception DeSome

let desome x = match x with Some x -> x | None -> raise DeSome

let option_map f o = match o with None -> None | Some e -> Some (f e)

let add_cons x l = if List.mem x l then l else x :: l

(* XXX: UNUSED *)
(* let rec remove_duplicates l =
 *   match l with [] -> [] | t :: q -> add_cons t (remove_duplicates q) *)

(* XXX: UNUSED *)
(* let position pred l =
 *   let rec pos p l =
 *     match l with
 *     | [] ->
 *       assert false
 *     | t :: q ->
 *       if pred t then p else pos (p + 1) q
 *   in
 *   pos 0 l *)

(* TODO: Lélio: why n+1? cf former def below *)
(* if n < 0 then [] else x :: duplicate x (n - 1) *)
let duplicate x n = List.init (n + 1) (fun _ -> x)

let enumerate n = List.init n (fun i -> i)

let rec repeat n f x = if n <= 0 then x else repeat (n - 1) f (f x)

let transpose_list ll =
  let rec transpose ll =
    match ll with
    | [] ->
      []
    | [ l ] ->
      List.map (fun el -> [ el ]) l
    | l :: q ->
      List.map2 (fun el eq -> el :: eq) l (transpose q)
  in
  match ll with
  | [] ->
    []
  | l :: q ->
    let length_l = List.length l in
    List.iter
      (fun l' ->
        let length_l' = List.length l' in
        if length_l <> length_l' then
          raise (TransposeError (length_l, length_l')))
      q;
    transpose ll

(* XXX: UNUSED *)
(* let rec filter_upto p n l =
 *   if n = 0 then []
 *   else
 *     match l with
 *     | [] ->
 *       []
 *     | t :: q ->
 *       if p t then t :: filter_upto p (n - 1) q else filter_upto p n q *)

(* XXX: UNUSED *)
(** [gcd a b] returns the greatest common divisor of [a] and [b]. *)
(* let rec gcd a b = if b = 0 then a else gcd b (a mod b) *)

(* XXX: UNUSED *)
(** [lcm a b] returns the least common multiple of [a] and [b]. *)
(* let lcm a b = if a = 0 && b = 0 then 0 else a * b / gcd a b *)

(* XXX: UNUSED *)
(** [sum_rat (a,b) (a',b')] returns the sum of rationals [(a,b)] and [(a',b')] *)
(* let sum_rat (a, b) (a', b') =
 *   if a = 0 && b = 0 then a', b'
 *   else if a' = 0 && b' = 0 then a, b
 *   else
 *     let lcm_bb' = lcm b b' in
 *     (a * lcm_bb' / b) + (a' * lcm_bb' / b'), lcm_bb' *)

(* XXX: UNUSED *)
(* let simplify_rat (a, b) =
 *   let gcd = gcd a b in
 *   if gcd = 0 then a, b else a / gcd, b / gcd *)

(* XXX: UNUSED *)
(* let max_rat (a, b) (a', b') =
 *   let ratio_ab = float_of_int a /. float_of_int b in
 *   let ratio_ab' = float_of_int a' /. float_of_int b' in
 *   if ratio_ab > ratio_ab' then a, b else a', b' *)

(** [list_union l1 l2] returns the union of list [l1] and [l2]. The result
    contains no duplicates. *)
let list_union l1 l2 =
  let rec aux l acc =
    match l with
    | [] ->
      acc
    | x :: tl ->
      if List.mem x acc then aux tl acc else aux tl (x :: acc)
  in
  let l1' = aux l1 [] in
  aux l2 l1'

(* XXX: UNUSED *)
(** [hashtbl_add h1 h2] adds all the bindings in [h2] to [h1]. If the
    intersection is not empty, it replaces the former binding *)
(* let hashtbl_add h1 h2 =
 *   Hashtbl.iter (fun key value -> Hashtbl.replace h1 key value) h2 *)

(* XXX: UNUSED *)
(* let hashtbl_iterlast h f1 f2 =
 *   let l = Hashtbl.length h in
 *   ignore
 *     (Hashtbl.fold
 *        (fun k v cpt ->
 *          if cpt = l then (
 *            f2 k v;
 *            cpt + 1)
 *          else (
 *            f1 k v;
 *            cpt + 1))
 *        h 1) *)

(** Match types variables to 'a, 'b, ..., for pretty-printing. Type variables
    are identified by integers. *)
let tnames = ref ([] : (int * string) list)

let tname_counter = ref 0

(* Same for carriers *)
let crnames = ref ([] : (int * string) list)

let crname_counter = ref 0

(* Same for dimension *)
let dnames = ref ([] : (int * string) list)

let dname_counter = ref 0

(* Same for delays *)
let inames = ref ([] : (int * string) list)

let iname_counter = ref 0

let reset_names () =
  tnames := [];
  tname_counter := 0;
  crnames := [];
  crname_counter := 0;
  dnames := [];
  dname_counter := 0;
  inames := [];
  iname_counter := 0

(* From OCaml compiler *)
let new_tname () =
  let tname =
    if !tname_counter < 26 then String.make 1 (Char.chr (97 + !tname_counter))
    else
      String.make 1 (Char.chr (97 + (!tname_counter mod 26)))
      ^ string_of_int (!tname_counter / 26)
  in
  incr tname_counter;
  tname

let new_crname () =
  incr crname_counter;
  Format.sprintf "c%i" (!crname_counter - 1)

let name_of_type id =
  try List.assoc id !tnames
  with Not_found ->
    let name = new_tname () in
    tnames := (id, name) :: !tnames;
    name

let name_of_carrier id =
  let pp_id =
    try List.assoc id !crnames
    with Not_found ->
      let name = new_crname () in
      crnames := (id, name) :: !crnames;
      name
  in
  pp_id

let new_dname () =
  incr dname_counter;
  Format.sprintf "d%i" (!dname_counter - 1)

let name_of_dimension id =
  try List.assoc id !dnames
  with Not_found ->
    let name = new_dname () in
    dnames := (id, name) :: !dnames;
    name

let new_iname () =
  incr iname_counter;
  Format.sprintf "t%i" (!iname_counter - 1)

let name_of_delay id =
  try List.assoc id !inames
  with Not_found ->
    let name = new_iname () in
    inames := (id, name) :: !inames;
    name

(* XXX: UNUSED *)
(* let print_rat fmt (a, b) =
 *   if b = 1 then Format.fprintf fmt "%i" a
 *   else if b < 0 then Format.fprintf fmt "%i/%i" (-a) (-b)
 *   else Format.fprintf fmt "%i/%i" a b *)

(* Generic pretty printing *)

module Format = struct
  include Format
  open Format

  let with_out_file file f =
    let oc = open_out file in
    let fmt = formatter_of_out_channel oc in
    f fmt;
    close_out oc

  let pp_print_nothing _fmt _ = ()

  let pp_print_cutcut fmt () = fprintf fmt "@,@,"

  let pp_print_endcut s fmt () = fprintf fmt "%s@," s

  let pp_print_opar fmt () = pp_print_string fmt "("

  let pp_print_cpar fmt () = pp_print_string fmt ")"

  let pp_print_obracket fmt () = pp_print_string fmt "["

  let pp_print_cbracket fmt () = pp_print_string fmt "]"

  let pp_print_obrace fmt () = pp_print_string fmt "{"

  let pp_print_cbrace fmt () = pp_print_string fmt "}"

  let pp_print_obrace' fmt () = pp_print_string fmt "{ "

  let pp_print_cbrace' fmt () = pp_print_string fmt " }"

  let pp_print_comma fmt () = fprintf fmt ",@ "

  let pp_print_semicolon fmt () = fprintf fmt ";@ "

  let pp_print_comma' fmt () = fprintf fmt ","

  let pp_print_semicolon' fmt () = fprintf fmt ";"

  let pp_open_vbox0 fmt () = pp_open_vbox fmt 0

  let pp_print_list ?(pp_prologue = pp_print_nothing)
      ?(pp_epilogue = pp_print_nothing) ?(pp_op = pp_print_nothing)
      ?(pp_cl = pp_print_nothing)
      ?(pp_open_box = fun fmt () -> pp_open_box fmt 0)
      ?(pp_eol = pp_print_nothing) ?(pp_nil = pp_print_nothing) ?pp_sep pp_v fmt
      l =
    fprintf
      fmt
      "%a%a%a%a%a@]%a%a"
      (fun fmt l -> if l <> [] then pp_prologue fmt ())
      l
      pp_op
      ()
      pp_open_box
      ()
      (fun fmt () ->
        if l = [] then pp_nil fmt () else pp_print_list ?pp_sep pp_v fmt l)
      ()
      (fun fmt l -> if l <> [] then pp_eol fmt ())
      l
      pp_cl
      ()
      (fun fmt l -> if l <> [] then pp_epilogue fmt ())
      l

  let pp_comma_list = pp_print_list ~pp_sep:pp_print_comma

  let pp_print_list_i ?pp_prologue ?pp_epilogue ?pp_op ?pp_cl ?pp_open_box
      ?pp_eol ?pp_nil ?pp_sep pp_v =
    let i = ref 0 in
    pp_print_list
      ?pp_prologue
      ?pp_epilogue
      ?pp_op
      ?pp_cl
      ?pp_open_box
      ?pp_eol
      ?pp_nil
      ?pp_sep
      (fun fmt x ->
        pp_v fmt !i x;
        incr i)

  let pp_print_list_i2 ?pp_prologue ?pp_epilogue ?pp_op ?pp_cl ?pp_open_box
      ?pp_eol ?pp_nil ?pp_sep pp_v fmt (l1, l2) =
    pp_print_list_i
      ?pp_prologue
      ?pp_epilogue
      ?pp_op
      ?pp_cl
      ?pp_open_box
      ?pp_eol
      ?pp_nil
      ?pp_sep
      (fun fmt i (x1, x2) -> pp_v fmt i x1 x2)
      fmt
      (List.combine l1 l2)

  let pp_print_parenthesized ?(pp_sep = pp_print_comma) =
    pp_print_list ~pp_op:pp_print_opar ~pp_cl:pp_print_cpar ~pp_sep

  let pp_print_bracketed ?(pp_sep = pp_print_comma) =
    pp_print_list ~pp_op:pp_print_obracket ~pp_cl:pp_print_cbracket ~pp_sep

  let pp_print_braced ?(pp_sep = pp_print_comma) =
    pp_print_list ~pp_op:pp_print_obrace ~pp_cl:pp_print_cbrace ~pp_sep

  let pp_print_braced' ?(pp_sep = pp_print_comma) =
    pp_print_list ~pp_op:pp_print_obrace' ~pp_cl:pp_print_cbrace' ~pp_sep
end

let pp_date fmt tm =
  let open Unix in
  Format.fprintf
    fmt
    "%i/%i/%i, %02i:%02i:%02i"
    (tm.tm_year + 1900)
    tm.tm_mon
    tm.tm_mday
    tm.tm_hour
    tm.tm_min
    tm.tm_sec

(* Used for uid in variables *)

(* XXX: UNUSED *)
(* let get_new_id =
 *   let var_id_cpt = ref 0 in
 *   fun () ->
 *     incr var_id_cpt;
 *     !var_id_cpt *)

let new_tag =
  let last_tag = ref (-1) in
  fun () ->
    incr last_tag;
    !last_tag

(* XXX: UNUSED *)
(* module List = struct
 *   include List
 *
 *   let iteri2 f l1 l2 =
 *     if List.length l1 <> List.length l2 then
 *       raise (Invalid_argument "iteri2: lists have different lengths")
 *     else
 *       let rec run idx l1 l2 =
 *         match l1, l2 with
 *         | [], [] ->
 *           ()
 *         | hd1 :: tl1, hd2 :: tl2 ->
 *           f idx hd1 hd2;
 *           run (idx + 1) tl1 tl2
 *         | _ ->
 *           assert false
 *       in
 *       run 0 l1 l2
 *
 *   let rec extract l fst last =
 *     if last < fst then assert false
 *     else
 *       match l, fst with
 *       | hd :: tl, 0 ->
 *         if last = 0 then [] else hd :: extract tl 0 (last - 1)
 *       | _ :: tl, _ ->
 *         extract tl (fst - 1) (last - 1)
 *       | [], 0 ->
 *         if last = 0 then [] else assert false (\* List too short *\)
 *       | _ ->
 *         assert false
 * end *)

(* XXX: UNUSED *)
(* let get_date () =
 *   let tm = Unix.localtime (Unix.time ()) in
 *   let fmt = Format.str_formatter in
 *   pp_date fmt tm;
 *   Format.flush_str_formatter () *)

(* Local Variables: *)
(* compile-command:"make -C .." *)
(* End: *)
