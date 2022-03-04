open Wp

(* check that a given predicate name is a transition and return its index *)
let is_transition (f: Lang.lfun) : int option =
  let open Str in
  let r = regexp "_transition\\([0-9]+\\)$" in
  let s = Repr.lfun f in
  try
    ignore (search_forward r s 0);
    Some (int_of_string (matched_group 1 s))
  with Not_found -> None

(* check that a given predicate name is a transition with given index *)
let is_transition_n (n: int) (f: Lang.lfun) : bool =
  let open Str in
  let r = regexp ("_transition" ^ string_of_int n ^ "$") in
  try ignore (search_forward r (Repr.lfun f) 0); true with Not_found -> false

(* check that a given predicate name is a memory pack simulation *)
let is_pack (f: Lang.lfun) : bool =
  let open Str in
  let r = regexp "_pack\\(\|[0-9]+\|_base\\)$" in
  let s = Repr.lfun f in
  try
    ignore (search_forward r s 0);
    true
  with Not_found -> false

(* check that a given predicate name is a reset_cleared relation *)
let is_reset_cleared (f: Lang.lfun) : bool =
  let open Str in
  let r = regexp "_reset_cleared$" in
  let s = Repr.lfun f in
  try
    ignore (search_forward r s 0);
    true
  with Not_found -> false

(* tactical selection of the goal *)
let select_g (g: Lang.F.pred) : Tactical.selection =
  let open Tactical in
  Clause (Goal g)

(* tactical selection of an hypothesis *)
let select_h (h: Conditions.step) : Tactical.selection =
  let open Tactical in
  Clause (Step h)

(* get variables and predicate under existential binder *)
let existential_vars_g (g: Lang.F.pred) : Lang.F.var list * Lang.F.term =
  let open Lang.F in
  let vars, g = e_open ~forall:false ~lambda:false ~pool:(pool ()) (e_prop g) in
  List.map snd vars, g

(* find the index of the first element that verifies p in l *)
let find_index p l =
  let rec aux i = function
    | [] -> raise Not_found
    | x :: l -> if p x then i else aux (i + 1) l
  in
  aux 0 l

(* check if the term t is the variable v *)
let is_var (v: Lang.F.var) (t: Lang.F.term) : bool =
  match Repr.term t with
  | Var w -> v = w
  | _ -> false

exception Found of Tactical.selection list

(* a function to search a transition call in the hypotheses *)
(*  that can be unified with a term *)
let rec unify
    (push: Strategy.strategy -> unit)
    (sequent: Conditions.sequent)
    (vars: Lang.F.var list)
    (term: Lang.F.term) : unit =
  let hyps = fst sequent in
  match Repr.term term with
  | Call (p, ts) ->
    (* get the index of the transition under the binder *)
    begin match is_transition p with
      | Some n ->
        (* find the indexes of the existential variables *)
        let idxs = List.map (fun v -> find_index (is_var v) ts) vars in
        (* we search the hypotheses to find the corresponding terms *)
        Conditions.iter (fun step -> match step.condition with
            | Have p ->
              (* in case of footprint lemma : unfold the hypothesis *)
              begin match Repr.pred p with
                | Call (p, _) when is_transition_n (n + 1) p ->
                  push (Auto.definition (select_h step))
                | _ -> ()
              end;
              (* a function to find an hypothesis *)
              let find_hyp term =
                match Repr.term term with
                | Call (p, ts) when is_transition_n n p ->
                  let witnesses = List.map (fun i ->
                      let t = List.nth ts i in
                      Strategy.select_e sequent t) idxs
                  in
                  raise (Found witnesses)
                | _ -> ()
              in
              let p = Lang.F.e_prop p in
              (* is the whole hypothesis the transition call? *)
              find_hyp p;
              (* otherwise, explore sub-terms to find it *)
              Lang.F.lc_iter find_hyp p
            | _ -> ()) hyps
      | None -> ()
    end

  | HigherOrder ->
    let pool = Lang.F.pool () in
    let fv = Lang.F.e_vars term in
    List.iter (Lang.F.add_var pool) fv;
    let qvars, term = Lang.F.e_open ~forall:false ~lambda:false ~pool term in
    unify push sequent vars term

  | _ ->
    Lang.F.lc_iter (unify push sequent vars) term

(* Transitions heuristic *)
class lustrec_transitions : Strategy.heuristic =
  object
    method id = "LustreC:Transitions" (* required, must be unique *)
    method title = "LustreC Transitions"
    method descr = "Custom goal transformations for transition relations"

    method search (push: Strategy.strategy -> unit) (sequent: Conditions.sequent)
      : unit =
      let goal = snd sequent in
      match Repr.pred goal with
      (* if the goal is only a transition relation, unfold it *)
      | Call (p, _) when is_transition p <> None ->
        push (Auto.definition (select_g goal))

      (* if the goal is existential *)
      | HigherOrder ->
        (* get the existential variables *)
        let vars, g = existential_vars_g goal in
        (* find the transition call under binders *)
        begin try unify push sequent vars g with
          | Found witnesses ->
            (* instantiate the variables with found (rev ??) witnesses *)
            push (Auto.instance (select_g goal) (List.rev witnesses));
          | _ -> ()
        end

      | _ -> ()
  end

(* Reset Cleared heuristic *)
class lustrec_reset_cleared : Strategy.heuristic =
  object
    method id = "LustreC:ResetCleared" (* required, must be unique *)
    method title = "LustreC ResetCleared"
    method descr = "Custom goal transformations for reset_cleared relations"

    method search (push: Strategy.strategy -> unit) (sequent: Conditions.sequent)
      : unit =
      let goal = snd sequent in
      match Repr.pred goal with
      (* if the goal is only a reset_cleared relation, unfold it *)
      | Call (p, _) when is_reset_cleared p ->
        push (Auto.definition (select_g goal))

      | _ -> ()
  end

(* unfold f(es) in the given context (context is handled with side-effects) *)
let definition
    (context: WpContext.context) (f: Lang.lfun) (es: Lang.F.term list)
  : Lang.F.term =
  let d = WpContext.on_context context Definitions.find_symbol f in
  match d.d_definition with
  | Predicate (_, p) ->
    let sigma = Lang.subst d.d_params es in
    Lang.F.e_prop (Lang.F.p_subst sigma p)
  | _ ->
    assert false

(* rewrite a sequent by unfolding a top-level memory pack relation *)
let unfold_process
    (context: WpContext.context) (t: Lang.F.term) (sequent: Conditions.sequent)
  : Conditions.sequent option =
  match Repr.term t with
  | Call (p, es) when is_pack p ->
    let v = definition context p es in
    Some (Conditions.subst (fun t' -> if t == t' then v else t') sequent)
  | _ -> None

(* sequent equality *)
let eq_sequent s1 s2 =
  Lang.F.eqp (snd s1) (snd s2)

(* rewrite a sequent by recursively unfolding memory pack relations, by *)
(* iterating over sub-terms *)
let rec rewrite_process
    (context: WpContext.context) (sequent: Conditions.sequent)
  : Conditions.sequent =
  let goal = Lang.F.e_prop (snd sequent) in
  (* first try to unfold the whole term *)
  match unfold_process context goal sequent with
  | Some sequent' ->
    if eq_sequent sequent' sequent
    then sequent
    else rewrite_process context sequent'
  | None ->
    (* otherwise try to unfold the first matching sub-term *)
    let exception Found of Conditions.sequent in
    try
      Lang.F.lc_iter (fun t ->
          match unfold_process context t sequent with
          | Some sequent' ->
            if not (eq_sequent sequent' sequent) then raise (Found sequent')
          | None ->
            ())
        goal;
      sequent
    with Found sequent' -> rewrite_process context sequent'

(* Memory Packs tactical *)
class unfold_rec =
  object
    inherit Tactical.make ~id:"LustreC.unfold"
        ~title:"Unfold rec MemoryPacks"
        ~descr:"Unfold recursively MemoryPacks relations"
        ~params:[]

    method select _feedback (_s: Tactical.selection) =
      let context = WpContext.get_context () in
      Tactical.Applicable (fun sequent -> [ "", rewrite_process context sequent ])

  end

(* Memory Packs strategy *)
let unfold_rec_strategy = Strategy.make (new unfold_rec) ~arguments:[]

(* Memory Packs heuristic *)
class lustrec_memory_packs : Strategy.heuristic =
  object
    method id = "LustreC:MemoryPacks" (* required, must be unique *)
    method title = "LustreC MemoryPacks"
    method descr = "Custom goal transformations for memory_pack relations"

    method search (push: Strategy.strategy -> unit) (sequent: Conditions.sequent)
      : unit =
      let goal = snd sequent in
      match Repr.pred goal with
      (* if the goal is only a memory_pack relation, unfold it recursively *)
      | Call (p, _) when is_pack p ->
        push (unfold_rec_strategy (select_g goal))

      (* split conjunctions and conditionnals *)
      | And _
      | If _ ->
        push (Auto.split (select_g goal))

      | _ -> ()
  end

(* Register the strategies *)
let () =
  Strategy.register (new lustrec_transitions);
  Strategy.register (new lustrec_reset_cleared);
  Strategy.register (new lustrec_memory_packs)
