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

(** Types definitions and a few utility functions on delay types. Delay analysis
    by type polymorphism instead of constraints *)

type t = { mutable ddesc : delay_desc; did : int }

and delay_desc =
  | Dvar (* Monomorphic type variable *)
  | Dundef
  | Darrow of t * t
  | Dtuple of t list
  | Dlink of t
  (* During unification, make links instead of substitutions *)
  | Dunivar
(* Polymorphic type variable *)

let new_id = ref (-1)

let new_delay desc =
  incr new_id;
  { ddesc = desc; did = !new_id }

let new_var () = new_delay Dvar

let new_univar () = new_delay Dunivar

(* XXX: UNUSED *)
(* let rec repr = function { ddesc = Dlink i'; _ } -> repr i' | i -> i *)

(* XXX: UNUSED *)
(** Splits [ty] into the [lhs,rhs] of an arrow type. Expects an arrow type
    (ensured by language syntax) *)
(* let split_arrow de =
 *   match (repr de).ddesc with
 *   | Darrow (din, dout) ->
 *     din, dout
 *   (\* Functions are not first order, I don't think the var case needs to be
 *      considered here *\)
 *   | _ ->
 *     failwith "Internal error: not an arrow type" *)

(* XXX: UNUSED *)
(** Returns the type corresponding to a type list. *)
(* let of_delay_list de =
 *   if List.length de > 1 then new_delay (Dtuple de) else List.hd de *)

(* XXX: UNUSED *)
(** [is_polymorphic de] returns true if [de] is polymorphic. *)
(* let rec is_polymorphic de =
 *   match de.ddesc with
 *   | Dvar ->
 *     false
 *   | Dundef ->
 *     false
 *   | Darrow (de1, de2) ->
 *     is_polymorphic de1 || is_polymorphic de2
 *   | Dtuple dl ->
 *     List.exists is_polymorphic dl
 *   | Dlink d' ->
 *     is_polymorphic d'
 *   | Dunivar ->
 *     true *)

(* Pretty-print*)

(* XXX: UNUSED *)
(* let rec pp fmt de =
 *   match de.ddesc with
 *   | Dvar ->
 *     fprintf fmt "'_%s" (name_of_type de.did)
 *   | Dundef ->
 *     fprintf fmt "1"
 *   | Darrow (de1, de2) ->
 *     fprintf fmt "%a->%a" pp de1 pp de2
 *   | Dtuple delist ->
 *     fprintf fmt "(%a)" (pp_print_list ~pp_sep:(fun fmt () -> pp_print_string fmt "*")
 *                           pp) delist
 *   | Dlink de ->
 *     pp fmt de
 *   | Dunivar ->
 *     fprintf fmt "'%s" (name_of_delay de.did) *)
