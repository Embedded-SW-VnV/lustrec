open Lustre_types
open Spec_types

(* a small reduction engine *)
let is_true = function
  | True -> true
  | _ -> false

let is_false = function
  | False -> true
  | _ -> false

let expr_eq: type a b. (a, left_v) expression_t -> (a, b) expression_t -> bool =
  fun a b ->
  match a, b with
  | Var x, Var y -> x = y
  | Memory r1, Memory r2 -> r1 = r2
  | _ -> false

let rec red: type a. a formula_t -> a formula_t = function
  | Equal (a, b) when expr_eq a b ->
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
    if is_true p' then True else begin match x with
      | [] -> p'
      | x -> Exists (x, p')
    end

  | Forall (x, p) ->
    let p' = red p in
    if is_true p' then True else begin match x with
      | [] -> p'
      | x -> Forall (x, p')
    end

  | Ternary (x, a, b) ->
    let a' = red a in
    let b' = red b in
    Ternary (x, a', b')

  | f -> f

(* smart constructors *)
(* let mk_condition x l =
 *   if l = tag_true then Ternary (Val x, True, False)
 *   else if l = tag_false then Ternary (Val x, False, True)
 *   else Equal (Val x, Tag l) *)

let vals vs = List.map (fun v -> Val v) vs

let mk_pred_call pred =
  Predicate pred

(* let mk_clocked_on id =
 *   mk_pred_call (Clocked_on id) *)

let mk_transition ?i ?inst id inputs locals outputs =
  mk_pred_call
    (Transition (id, inst, i, vals inputs, vals locals, vals outputs))

let mk_memory_pack ?i ?inst id =
  mk_pred_call (MemoryPack (id, inst, i))

let mk_state_variable_pack x =
  StateVarPack (StateVar x)

let mk_state_assign_tr x v =
  Equal (Memory (StateVar x), Val v)

let mk_conditional_tr v t f =
  Ternary (Val v, t, f)

let mk_branch_tr x hl =
  And (List.map (fun (t, spec) -> Imply (Equal (Var x, Tag t), spec)) hl)

let mk_assign_tr x v =
  Equal (Var x, Val v)

