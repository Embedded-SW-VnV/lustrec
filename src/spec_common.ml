open Spec_types
open Utils

(* a small reduction engine *)
let is_true = function True -> true | _ -> false

let is_false = function False -> true | _ -> false

let type_of_l_value = function
  | Var v ->
    v.var_type
  | Memory ResetFlag ->
    Type_predef.type_bool
  | Memory (StateVar v) ->
    v.var_type
  | _ -> assert false

let expr_eq a b =
  match a, b with
  | Var x, Var y ->
    x = y
  | Memory r1, Memory r2 ->
    r1 = r2
  | _ ->
    false

let rec red = function
  | Equal (a, b) when expr_eq a b ->
    True
  | And l -> (
    let l' =
      List.filter_map
        (fun a ->
          let a' = red a in
          if is_true a' then None else Some a')
        l
    in
    match l' with
    | [] ->
      True
    | [ a ] ->
      a
    | l' when List.exists is_false l' ->
      False
    | _ ->
      And l')
  | Or l -> (
    let l' =
      List.filter_map
        (fun a ->
          let a' = red a in
          if is_false a' then None else Some a')
        l
    in
    match l' with
    | [] ->
      assert false
    | [ a ] ->
      a
    | l' when List.exists is_true l' ->
      True
    | _ ->
      Or l')
  | Imply (a, b) ->
    let a' = red a in
    let b' = red b in
    if a' = b' || is_false a' || is_true b' then True
    else if is_true a' then b'
    else Imply (a', b')
  | Exists (x, p) -> (
    let p' = red p in
    if is_true p' then True else match x with [] -> p' | x -> Exists (x, p'))
  | Forall (x, p) -> (
    let p' = red p in
    if is_true p' then True else match x with [] -> p' | x -> Forall (x, p'))
  | Ternary (x, a, b) ->
    let a' = red a in
    let b' = red b in
    Ternary (x, a', b')
  | f ->
    f

(* smart constructors *)

let vals vs = List.map (fun v -> Val v) vs

let mk_pred_call pred = Predicate pred

let mk_transition ?(mems = ISet.empty) ?(insts = IMap.empty) ?r ?i ?inst
    stateless id vars =
  let tr =
    mk_pred_call
      (Transition
         ( stateless,
           id,
           inst,
           i,
           vals vars,
           (match r with Some _ -> true | None -> false),
           mems,
           insts ))
  in
  match r, inst with
  | Some r, Some inst ->
    ExistsMem (id, mk_pred_call (Reset (id, inst, r)), tr)
  | _ ->
    tr

let mk_memory_pack ?i ?inst id = mk_pred_call (MemoryPack (id, inst, i))

let mk_state_variable_pack x = StateVarPack (StateVar x)

let mk_state_assign_tr x v = Equal (Memory (StateVar x), Val v)

let mk_conditional_tr v t f = Ternary (Val v, t, f)

let mk_branch_tr x =
  let open Lustre_types in
  function
  | [ (h1, spec1); (h2, spec2) ] when h1 = tag_true && h2 = tag_false ->
    Ternary (Var x, spec1, spec2)
  | [ (h1, spec1); (h2, spec2) ] when h1 = tag_false && h2 = tag_true ->
    Ternary (Var x, spec2, spec1)
  | hl ->
    let n = List.length hl in
    And (List.mapi (fun k (t, spec) ->
        let c = if k = n - 1 then GEqual (Var x, Tag t) else Equal (Var x, Tag t) in
        Imply (c, spec)) hl)

let mk_assign_tr x v = Equal (Var x, Val v)
