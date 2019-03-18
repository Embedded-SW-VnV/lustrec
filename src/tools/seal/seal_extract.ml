open Lustre_types
open Utils
open Seal_utils			

(* Switched system extraction *)
type element = IsInit | Expr of expr
type guard = (element * bool) list
type guarded_expr = guard * element
type mdef_t = guarded_expr list

let pp_elem fmt e =
  match e with
  | IsInit -> Format.fprintf fmt "init"
  | Expr e -> Printers.pp_expr fmt e

let pp_guard_expr fmt (gl,e) =
  Format.fprintf fmt "%a -> %a"
    (fprintf_list ~sep:"; "
       (fun fmt (e,b) -> if b then pp_elem fmt e else Format.fprintf fmt "not(%a)" pp_elem e)) gl
    pp_elem e

let pp_mdefs fmt gel = fprintf_list ~sep:"@ " pp_guard_expr fmt gel

  
let add_init defs vid =
  Hashtbl.add defs vid [[], IsInit]

let deelem e =  match e with
    Expr e -> e
  | IsInit -> assert false (* Wasn't expecting isinit here: we are building values! *)

let is_eq_elem elem elem' =
  match elem, elem' with
  | IsInit, IsInit -> true
  | Expr e, Expr e' ->
     Corelang.is_eq_expr e e'
  | _ -> false

let select_elem elem (gelem, _) =
  is_eq_elem elem gelem

  
let combine_guards ?(fresh=None) gl1 gl2 =
  (* Filtering out trivial cases. More semantics ones would have to be
     addressed later *)
  let check (gexpr, posneg) l =
    (* Check if gepxr is part of l *)
    let sel_fun = select_elem gexpr in
    if List.exists sel_fun l then
      (* Checking the guard value posneg *)
      let _, status = List.find sel_fun l in
      status=posneg, l
    else
      (* Valid: no overlap *)
      true, (gexpr, posneg)::l
  in
  let ok, gl =
    List.fold_left (
        fun (ok, l) g ->
        (* Bypass for negative output *)
        if not ok then false, []
        else
          check g l 
      ) (true, gl2) gl1
  in
  if ok then
    match fresh with
      None -> true, gl
    | Some fresh_g -> (
    (* Checking the fresh element *)
      check fresh_g gl
    )
  else
    ok, []

(* Encode "If gel1=posneg then gel2":
   - Compute the combination of guarded exprs in gel1 and gel2:
     - Each guarded_expr in gel1 is transformed as a guard: the
       expression is associated to posneg.
     - Existing guards in gel2 are concatenated to that list of guards
     - We keep expr in the ge of gel2 as the legitimate expression 
 *)
let concatenate_ge gel1 posneg gel2 =
  List.fold_left (
      fun accu (g2,e2) ->
      List.fold_left (
          fun accu (g1,e1) ->
          let ok, gl = combine_guards ~fresh:(Some(e1,posneg)) g1 g2 in
          if ok then
            (gl, e2)::accu
          else
            accu
        ) accu gel1
    ) [] gel2

let rec rewrite defs expr : guarded_expr list =
  let rewrite = rewrite defs in
  match expr.expr_desc with
  | Expr_appl (id, args, None) ->
     let args = rewrite args in
     List.map (fun (guards, e) ->
           guards,
           Expr {expr with expr_desc = Expr_appl(id, deelem e, None)}
       ) args 
  | Expr_const _  -> [[], Expr expr]
  | Expr_ident id ->
     if Hashtbl.mem defs id then
       Hashtbl.find defs id
     else
       (* id should be an input *)
       [[], Expr expr]
  | Expr_ite (g, e1, e2) ->
     let g = rewrite g and
         e1 = rewrite e1 and
         e2 = rewrite e2 in
     (concatenate_ge g true e1)@
       (concatenate_ge g false e2)
  | Expr_merge (g, branches) ->
     assert false (* TODO: deal with merges *)
    
  | Expr_when (e, _, _) -> rewrite e
  | Expr_arrow _ -> [[], IsInit] (* At this point the only arrow should be true -> false *)
  | Expr_tuple el ->
     (* Each expr is associated to its flatten guarded expr list *)
     let gell = List.map rewrite el in
     (* Computing all combinations: we obtain a list of guarded tuple *)
     let rec aux gell : (guard * expr list) list =
       match gell with
       | [] -> assert false (* Not happening *)
       | [gel] -> List.map (fun (g,e) -> g, [deelem e]) gel
       | gel::getl ->
          let getl = aux getl in
          List.fold_left (
              fun accu (g,e) ->
              List.fold_left (
                    fun accu (gl, minituple) ->
                    let is_compat, guard_comb = combine_guards g gl in
                    if is_compat then
                      let new_gt : guard * expr list = (guard_comb, (deelem e)::minituple) in
                      new_gt::accu
                    else
                      accu
                  
                  ) accu getl
            ) [] gel
     in
     let gtuples = aux gell in
     (* Rebuilding the valid type: guarded expr list (with tuple exprs) *)
     List.map (fun (g,tuple) -> g, Expr {expr with expr_desc = Expr_tuple tuple}) gtuples
  | Expr_fby _
    | Expr_appl _
                (* Should be removed by mormalization and inlining *)
    -> Format.eprintf "Pb expr: %a@.@?" Printers.pp_expr expr; assert false
  | Expr_array _ | Expr_access _ | Expr_power _
                                              (* Arrays not handled here yet *)
    -> assert false
  | Expr_pre _ -> (* Not rewriting mem assign *)
     assert false
and add_def defs vid expr =
  Hashtbl.add defs vid (rewrite defs expr)

(* Takes a list of guarded exprs (ge) and a guard
returns the same list of ge splited into the ones where the guard is true and the ones where it is false. In both lists the associated ge do not mention that guard anymore.

When a given ge doesn't mention positively or negatively such guards, it is duplicated in both lists *)
let split_mdefs elem (mdefs: guarded_expr list) =
  List.fold_left (
      fun (selected, left_out)
          ((guards, expr) as ge) ->
      (* select the element of guards that match the argument elem *)
      let sel, others_guards = List.partition (select_elem elem) guards in
      match sel with
      (* we extract the element from the list and add it to the
         appropriate list *)
      | [_, sel_status] ->
         if sel_status then
           (others_guards,expr)::selected, left_out
         else selected, (others_guards,expr)::left_out
      | [] -> (* no such guard exists, we have to duplicate the
              guard_expr in both lists *)
         ge::selected, ge::left_out
      | _ -> (
        Format.eprintf "@.Spliting list on elem %a.@.List:%a@."
          pp_elem elem
          pp_mdefs mdefs;
        assert false (* more then one element selected. Should
                          not happen , or trival dead code like if
                              x then if not x then dead code *)
      )
    ) ([],[]) mdefs
    
let split_mem_defs
      (elem: element)
      (mem_defs: (ident * guarded_expr list) list) :
      ((ident * mdef_t) list) * ((ident * mdef_t) list)
  =
  List.fold_right (fun (m,mdefs)
                       (accu_pos, accu_neg) ->
      let pos, neg =
        split_mdefs elem mdefs
      in
      (m, pos)::accu_pos,
      (m, neg)::accu_neg
    ) mem_defs ([],[])


(* Split a list of mem_defs into init and step lists of guarded
   expressions per memory. *)
let split_init mem_defs =
  split_mem_defs IsInit mem_defs

let pick_guard mem_defs : expr =
  let gel = List.flatten (List.map snd mem_defs) in
  let gl = List.flatten (List.map fst gel) in
  let all_guards =
    List.map (
        (* selecting guards and getting rid of boolean *)
        fun (e,b) ->
        match e with
        | Expr e -> e
        | _ -> assert false
      (* should have been filtered out
                                      yet *)
      ) gl
  in
  (* TODO , one could sort by occurence and provided the most common
     one *)
  List.hd all_guards  
  
(* Transform a list of variable * guarded exprs into a list of guarded pairs (variable, expressions)
*)
let rec build_switch_sys
          (mem_defs : (Utils.ident * guarded_expr list) list )
          prefix
        :
          ((expr * bool) list * (ident * expr) list ) list =
  (* if all mem_defs have empty guards, we are done, return prefix,
     mem_defs expr.

     otherwise pick a guard in one of the mem, eg (g, b) then for each
     other mem, one need to select the same guard g with the same status b, *)
  if List.for_all (fun (m,mdefs) ->
         (* All defs are unguarded *)
         match mdefs with
         | [[], _] -> true
         | _ -> false) mem_defs
  then
    [prefix ,
     List.map (fun (m,gel) ->
         match gel with
         | [_,e] ->
            let e =
              match e with
              | Expr e -> e
              | _ -> assert false (* No IsInit expression *)
            in
            m,e
         | _ -> assert false
       ) mem_defs]
  else
    (* Picking a guard *)
    let elem : expr = pick_guard mem_defs in
    let pos, neg =
      split_mem_defs
        (Expr elem)
        mem_defs
    in
    (* Special cases to avoid useless computations: true, false conditions *)
    match elem.expr_desc with
    | Expr_ident "true"  ->   build_switch_sys pos prefix
    | Expr_const (Const_tag tag) when tag = Corelang.tag_true
                         ->   build_switch_sys pos prefix
    | Expr_ident "false" ->   build_switch_sys neg prefix
    | Expr_const (Const_tag tag) when tag = Corelang.tag_false 
                         ->   build_switch_sys neg prefix
    | _ -> (* Regular case *)
       (* let _ = (
        *     Format.eprintf "Expr is %a@." Printers.pp_expr elem;
        *     match elem.expr_desc with
        *     | Expr_const _ -> Format.eprintf "a const@."
        *                     
        *     | Expr_ident _ -> Format.eprintf "an ident@."
        *     | _ -> Format.eprintf "something else@."
        *   )
        * in *)
       (build_switch_sys pos ((elem, true)::prefix))
       @
         (build_switch_sys neg ((elem, false)::prefix))
      


      
(* Take a normalized node and extract a list of switches: (cond,
   update) meaning "if cond then update" where update shall define all
   node memories. Everything as to be expressed over inputs or memories, intermediate variables are removed through inlining *)
let node_as_switched_sys (mems:var_decl list) nd =
  (* rescheduling node: has been scheduled already, no need to protect
     the call to schedule_node *)
  let nd_report = Scheduling.schedule_node nd in
  let schedule = nd_report.Scheduling_type.schedule in
  let eqs, auts = Corelang.get_node_eqs nd in
  assert (auts = []); (* Automata should be expanded by now *)
  let sorted_eqs = Scheduling.sort_equations_from_schedule eqs schedule in
  let defs : (ident,  guarded_expr list) Hashtbl.t = Hashtbl.create 13 in
  let add_def = add_def defs in
  (* Registering node equations *)
  let mem_defs =
    List.fold_left (fun accu eq ->
        match eq.eq_lhs with
        | [vid] ->
           (* Only focus on non memory definitions *)
           if not (List.exists (fun v -> v.var_id = vid) mems) then (
             report ~level:3 (fun fmt -> Format.fprintf fmt "Registering variable %s@." vid);
             add_def vid eq.eq_rhs;
             accu
           )
           else
             (
               match eq.eq_rhs.expr_desc with
               | Expr_pre def_m ->
                  report ~level:3 (fun fmt -> Format.fprintf fmt "Preparing mem %s@." vid);

                  (vid, rewrite defs def_m)::accu
               | _ -> assert false
             )
        | _ -> assert false (* should have been removed by normalization *)
      ) [] sorted_eqs
  in
  report ~level:2 (fun fmt -> Format.fprintf fmt "Printing out (guarded) memories definitions (may takes time)@.");
  (* Printing memories definitions *)
  report ~level:3
    (fun fmt ->
      Format.fprintf fmt
        "@[<v 0>%a@]@ "
        (Utils.fprintf_list ~sep:"@ "
           (fun fmt (m,mdefs) ->
             Format.fprintf fmt
               "%s -> [@[<v 0>%a@] ]@ "
               m
               (Utils.fprintf_list ~sep:"@ "
                  pp_guard_expr) mdefs
        ))
        mem_defs);
  let init_defs, update_defs =
    split_init mem_defs
  in
  report ~level:3
    (fun fmt ->
      Format.fprintf fmt
        "@[<v 0>Init:@ %a@ Step@ %a@]@ "
        (Utils.fprintf_list ~sep:"@ "
           (fun fmt (m,mdefs) ->
             Format.fprintf fmt
               "%s -> @[<v 0>[%a@] ]@ "
               m
               (Utils.fprintf_list ~sep:"@ "
                  pp_guard_expr) mdefs
        ))
        init_defs
        (Utils.fprintf_list ~sep:"@ "
           (fun fmt (m,mdefs) ->
             Format.fprintf fmt
               "%s -> @[<v 0>[%a@] ]@ "
               m
               (Utils.fprintf_list ~sep:"@ "
                  pp_guard_expr) mdefs
        ))
        update_defs);
  let sw_init= 
    build_switch_sys init_defs []
  in
  let sw_sys =
    build_switch_sys update_defs []
  in
  sw_init, sw_sys
