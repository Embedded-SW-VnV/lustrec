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
  let r = regexp "_pack\\([0-9]+\\)$" in
  let s = Repr.lfun f in
  try
    ignore (search_forward r s 0);
    true
  with Not_found -> false

(* tactical selection of the goal *)
let select_g (g: Lang.F.pred) : Tactical.selection =
  let open Tactical in
  Clause (Goal g)

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

class lustrec : Strategy.heuristic =
  object
    method id = "LustreC" (* required, must be unique *)
    method title = "LustreC" (* visible in Strategy panel *)
    method descr = "Custom goal transformations" (* idem *)

    method search (push: Strategy.strategy -> unit) (sequent: Conditions.sequent) : unit =
      let hyps, goal = sequent in
      match Repr.pred goal with
      (* if the goal is only a transition or memory pack call, unfold it *)
      | Call (p, _) when is_transition p <> None || is_pack p ->
        push (Auto.definition (select_g goal))

      (* if the goal is existential *)
      | HigherOrder ->
        (* get the existential variables *)
        let vars, g = existential_vars_g goal in
        let exception Found of Tactical.selection list in
        (* a function to search a transition call in the hypotheses *)
        (*  that can be unified with a term *)
        let unify term =
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
                      begin match Repr.pred p with
                        | Call (p, ts) when is_transition_n n p ->
                          let witnesses = List.map (fun i ->
                              let t = List.nth ts i in
                              Strategy.select_e sequent t) idxs
                          in
                          raise (Found witnesses)

                        | _ -> ()
                      end
                    | _ -> ()) hyps
              | None -> ()
            end
          | _ -> ()
        in
        begin try
            (* is the whole term a transition call ? *)
            unify g;
            (* otherwise, explore sub-terms to find a transition call *)
            Lang.F.lc_iter unify g
          with
          | Found witnesses ->
            (* instantiate the variables with found (rev ??) witnesses *)
            push (Auto.instance (select_g goal) (List.rev witnesses));
          | _ -> ()
        end

      | _ -> ()
  end

(* Register the strategy *)
let () = Strategy.register (new lustrec)
