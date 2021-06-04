open Lustre_types
open Spec_types

(* a small reduction engine *)
let is_true = function
  | True -> true
  | _ -> false

let is_false = function
  | False -> true
  | _ -> false

let rec red = function
  | Equal (a, b) when a = b ->
    True

  | And l ->
    let l' = List.filter_map (fun a ->
        let a' = red a in
        if is_true a' then None else Some a') l in
    begin match l' with
      | [] -> True
      | [a] -> a
      | l' when List.exists is_false l' -> False
      | _ -> And l'
    end

  | Or l ->
    let l' = List.filter_map (fun a ->
        let a' = red a in
        if is_false a' then None else Some a') l in
    begin match l' with
      | [] -> assert false
      | [a] -> a
      | l' when List.exists is_true l' -> True
      | _ -> Or l'
    end

  | Imply (a, b) ->
    let a' = red a in
    let b' = red b in
    if a' = b' || is_false a' || is_true b' then True
    else if is_true a' && is_false b' then False
    else Imply (a', b')

  | Exists (x, p) ->
    let p' = red p in
    if is_true p' then True else Exists (x, p')

  | Forall (x, p) ->
    let p' = red p in
    if is_true p' then True else Forall (x, p')

  | Ternary (x, a, b) ->
    let a' = red a in
    let b' = red b in
    Ternary (x, a', b')

  | f -> f

(* smart constructors *)
let mk_condition x l =
  if l = tag_true then Ternary (Val x, True, False)
  else if l = tag_false then Ternary (Val x, False, True)
  else Equal (Val x, Tag l)

let vals vs = List.map (fun v -> Val v) vs

let mk_pred_call pred vars =
  Predicate (pred, vals vars)

let mk_clocked_on id =
  mk_pred_call (Clocked_on id)

let mk_transition ?i id =
  mk_pred_call (Transition (id, i))

module type SPECVALUE = sig
  type t
  type ctx
  val pp_val: ctx -> Format.formatter -> t -> unit
end

module PrintSpec(SV: SPECVALUE) = struct

  open Utils.Format

  let pp_state fmt = function
    | In -> pp_print_string fmt "IN"
    | Out -> pp_print_string fmt "OUT"

  let pp_expr ctx fmt = function
    | Val v -> SV.pp_val ctx fmt v
    | Tag t -> pp_print_string fmt t
    | Var v -> pp_print_string fmt v.var_id
    | Instance (s, i) -> fprintf fmt "%a:%a" pp_state s pp_print_string i
    | Memory (s, i) -> fprintf fmt "%a:%a" pp_state s pp_print_string i

  let pp_predicate fmt = function
    | Clocked_on x -> fprintf fmt "On<%a>" pp_print_string x
    | Transition (f, i) ->
      fprintf fmt "Transition<%a>%a"
        pp_print_string f
        (pp_print_option pp_print_int) i
    | Initialization -> ()

  let pp_spec ctx =
    let pp_expr = pp_expr ctx in
    let rec pp_spec fmt f =
      match f with
      | True -> pp_print_string fmt "true"
      | False -> pp_print_string fmt "false"
      | Equal (a, b) ->
        fprintf fmt "%a == %a" pp_expr a pp_expr b
      | And fs ->
        pp_print_list ~pp_sep:(fun fmt () -> pp_print_string fmt "/\\") pp_spec fmt fs
      | Or fs ->
        pp_print_list ~pp_sep:(fun fmt () -> pp_print_string fmt "\\/") pp_spec fmt fs
      | Imply (a, b) ->
        fprintf fmt "%a -> %a" pp_spec a pp_spec b
      | Exists (xs, a) ->
        fprintf fmt "∃%a, %a" (pp_print_list Printers.pp_var) xs pp_spec a
      | Forall (xs, a) ->
        fprintf fmt "∀%a, %a" (pp_print_list Printers.pp_var) xs pp_spec a
      | Ternary (e, a, b) ->
        fprintf fmt "If %a Then %a Else %a" pp_expr e pp_spec a pp_spec b
      | Predicate (p, es) ->
        fprintf fmt "%a%a" pp_predicate p (pp_print_parenthesized pp_expr) es
    in
    pp_spec

end
