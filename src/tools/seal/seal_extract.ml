open Lustre_types
open Utils
open Seal_utils			
open Zustre_data (* Access to Z3 context *)
   

(* Switched system extraction *)
type element = IsInit | Expr of expr
type guard = (element * bool) list
type guarded_expr = guard * element
type mdef_t = guarded_expr list

let pp_elem fmt e =
  match e with
  | IsInit -> Format.fprintf fmt "init"
  | Expr e -> Printers.pp_expr fmt e

let pp_guard_list fmt gl =
  (fprintf_list ~sep:"; "
     (fun fmt (e,b) -> if b then pp_elem fmt e else Format.fprintf fmt "not(%a)" pp_elem e)) fmt gl
  
let pp_guard_expr fmt (gl,e) =
  Format.fprintf fmt "%a -> %a"
    pp_guard_list  gl
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


(**************************************************************)
(* Convert from Lustre expressions to Z3 expressions and back *)
(* All (free) variables have to be declared in the Z3 context *)
(**************************************************************)

let is_init_name = "__is_init"

let const_defs = Hashtbl.create 13
let is_const id = Hashtbl.mem const_defs id
let get_const id = Hashtbl.find const_defs id
                 
(* expressions are only basic constructs here, no more ite, tuples,
   arrows, fby, ... *)
let expr_to_z3_expr, zexpr_to_expr =
  (* List to store converted expression. *)
  let hash = ref [] in
  let comp_expr e (e', _) = Corelang.is_eq_expr e e' in
  let comp_zexpr ze (_, ze') = Z3.Expr.equal ze ze' in
  let mem_expr e = List.exists (comp_expr e) !hash in
  let mem_zexpr ze = List.exists (comp_zexpr ze) !hash in
  let get_zexpr e =
    let (_, ze) = List.find (comp_expr e) !hash in
    ze
  in
  let get_expr ze =
    let (e, _) = List.find (comp_zexpr ze) !hash in
    e
  in
  let add_expr e ze = hash := (e, ze)::!hash in
  let rec e2ze e =
    if mem_expr e then (
      get_zexpr e
    )
    else (
      let res =
        match e.expr_desc with
        | Expr_const c ->
           let z3e = Zustre_common.horn_const_to_expr c in
           add_expr e z3e;
           z3e
        | Expr_ident id -> (
          if is_const id then (
            let c = get_const id in
            let z3e = Zustre_common.horn_const_to_expr c in
            add_expr e z3e;
            z3e
        )
        else (
          let fdecl_id = Zustre_common.get_fdecl id in
          let z3e = Z3.Expr.mk_const_f !ctx fdecl_id in
          add_expr e z3e;
          z3e
          )
        )
      | Expr_appl (id,args, None) (* no reset *) ->
         let z3e = Zustre_common.horn_basic_app id e2ze (Corelang.expr_list_of_expr args) in
         add_expr e z3e;
         z3e
      | Expr_tuple [e] ->
         let z3e = e2ze e in
         add_expr e z3e;
         z3e
      | _ -> ( match e.expr_desc with Expr_tuple _ -> Format.eprintf "tuple e2ze(%a)@.@?" Printers.pp_expr e
                                    | _ -> Format.eprintf "e2ze(%a)@.@?" Printers.pp_expr e)
                 ; assert false
      in
      res
    )
  in
  let rec ze2e ze =
    let ze_name ze =
      let fd = Z3.Expr.get_func_decl ze in
      Z3.Symbol.to_string (Z3.FuncDecl.get_name fd)
    in
    if mem_zexpr ze then
      None, Some (get_expr ze)
    else
      let open Corelang in
      let fd = Z3.Expr.get_func_decl ze in
      let zel = Z3.Expr.get_args ze in
      match Z3.Symbol.to_string (Z3.FuncDecl.get_name fd), zel with
      (*      | var, [] -> (* should be in env *) get_e *)

      (* Extracting IsInit status *)
      | "not", [ze] when ze_name ze = is_init_name ->
         Some false, None
      | name, [] when name = is_init_name -> Some true, None
      (* Other constructs are converted to a lustre expression *)
      | op, _ -> (
        
        
        if Z3.Expr.is_numeral ze then
          let e =
            if Z3.Arithmetic.is_real ze then
              let num =  Num.num_of_ratio (Z3.Arithmetic.Real.get_ratio ze) in
              let s = Z3.Arithmetic.Real.numeral_to_string ze in
              mkexpr
                Location.dummy_loc
                (Expr_const
                   (Const_real
                      (num, 0, s)))
            else if Z3.Arithmetic.is_int ze then
              mkexpr
                Location.dummy_loc
                (Expr_const
                   (Const_int
                      (Big_int.int_of_big_int (Z3.Arithmetic.Integer.get_big_int ze))))
            else if Z3.Expr.is_const ze then
              match Z3.Expr.to_string ze with
              | "true" -> mkexpr Location.dummy_loc
                            (Expr_const (Const_tag (tag_true)))
              | "false" ->
                 mkexpr Location.dummy_loc
                   (Expr_const (Const_tag (tag_false)))
              | _ -> assert false
            else
              (
                Format.eprintf "Const err: %s %b@." (Z3.Expr.to_string ze) (Z3.Expr.is_const ze);
                assert false (* a numeral but no int nor real *)
              )
          in
          None, Some e
        else
          match op with
          | "not" | "=" | "-" | "*" | "/"
            | ">=" | "<=" | ">" | "<" 
            ->
             let args = List.map (fun ze -> Utils.desome (snd (ze2e ze))) zel in
             None, Some (mkpredef_call Location.dummy_loc op args)
          | "+" -> ( (* Special treatment of + for 2+ args *)
            let args = List.map (fun ze -> Utils.desome (snd (ze2e ze))) zel in
            let e = match args with
                [] -> assert false
              | [hd] -> hd
              | e1::e2::tl ->
                 let first_binary_and = mkpredef_call Location.dummy_loc op [e1;e2] in
                 if tl = [] then first_binary_and else
                   List.fold_left (fun e e_new ->
                       mkpredef_call Location.dummy_loc op [e;e_new]
                     ) first_binary_and tl
                 
            in
            None, Some e 
          )
          | "and" | "or" -> (
            (* Special case since it can contain is_init pred *)
            let args = List.map (fun ze -> ze2e ze) zel in
            let op = if op = "and" then "&&" else if op = "or" then "||" else assert false in 
            match args with
            | [] -> assert false
            | [hd] -> hd
            | hd::tl ->
               List.fold_left
                 (fun (is_init_opt1, expr_opt1) (is_init_opt2, expr_opt2) ->
                   (match is_init_opt1, is_init_opt2 with
                      None, x | x, None -> x
                      | Some _, Some _ -> assert false),
                   (match expr_opt1, expr_opt2 with
                    | None, x | x, None -> x
                    | Some e1, Some e2 ->
                       Some (mkpredef_call Location.dummy_loc op [e1; e2])
                 ))
                 hd tl 
          )
          | op -> 
             let args = List.map (fun ze ->  (snd (ze2e ze))) zel in
             Format.eprintf "deal with op %s (nb args: %i). Expr is %s@."  op (List.length args) (Z3.Expr.to_string ze); assert false
      )
  in
  (fun e -> e2ze e), (fun ze -> ze2e ze)

let is_init_z3e = Z3.Expr.mk_const_s !ctx is_init_name  Zustre_common.bool_sort 
let neg_ze z3e = Z3.Boolean.mk_not !ctx z3e 

let zexpr_to_guard_list ze =
  let init_opt, expr_opt = zexpr_to_expr ze in
  (match init_opt with
   | None -> []
   |Some b -> [IsInit, b]
  ) @ (match expr_opt with
       | None -> []
       | Some e -> [Expr e, true]
      )
let simplify_neg_guard l =
  List.map (fun (g,posneg) ->
      match g with
      | IsInit -> g, posneg
      | Expr g ->
          if posneg then
            Expr (Corelang.push_negations g),
            true
          else
            (* Pushing the negation in the expression *)
            Expr(Corelang.push_negations ~neg:true g),
            true
    ) l 

(* TODO:
individuellement demander si g1 => g2. Si c'est le cas, on peut ne garder que g1 dans la liste
*)    
(*****************************************************************)
(* Checking sat(isfiability) of an expression and simplifying it *)
(* All (free) variables have to be declared in the Z3 context    *)
(*****************************************************************)
let goal_simplify zl =
  let goal = Z3.Goal.mk_goal !ctx false false false in
  Z3.Goal.add goal zl;
  let goal' = Z3.Goal.simplify goal None in
  (* Format.eprintf "Goal before: %s@.Goal after : %s@.Sat? %s@."
   *   (Z3.Goal.to_string goal)
   *   (Z3.Goal.to_string goal')
   *   (Z3.Solver.string_of_status status_res) 
   * ; *)
  let ze = Z3.Goal.as_expr goal' in
  (* Format.eprintf "as an expr: %s@." (Z3.Expr.to_string ze); *)
  ze

let implies e1 e2 =
  (* Format.eprintf "Checking implication: %s => %s? "
   * (Z3.Expr.to_string e1) (Z3.Expr.to_string e2)
   * ; *)
  let solver = Z3.Solver.mk_simple_solver !ctx in
  let tgt = Z3.Boolean.mk_not !ctx (Z3.Boolean.mk_implies !ctx e1 e2) in
  try
    let status_res = Z3.Solver.check solver [tgt] in
    match status_res with
    | Z3.Solver.UNSATISFIABLE -> (* Format.eprintf "Valid!@."; *)
                                 true
    | _ -> (* Format.eprintf "not proved valid@."; *)
           false
  with Zustre_common.UnknownFunction(id, msg) -> (
    report ~level:1 msg;
    false
  )
                                               
let rec simplify zl =
  match zl with
  | [] | [_] -> zl
  | hd::tl -> (
  (* Forall e in tl, checking whether hd => e or e => hd, to keep hd
     in the first case and e in the second one *)
    let tl = simplify tl in
    let keep_hd, tl =
      List.fold_left (fun (keep_hd, accu) e ->
          if implies hd e then
            true, accu (* throwing away e *)
          else if implies e hd then
            false, e::accu (* throwing away hd *)
          else
            keep_hd, e::accu (* keeping both *)
        ) (true,[]) tl
    in
    (* Format.eprintf "keep_hd?%b hd=%s, tl=[%a]@."
     *   keep_hd
     *   (Z3.Expr.to_string hd)
     * (Utils.fprintf_list ~sep:"; " (fun fmt e -> Format.fprintf fmt "%s" (Z3.Expr.to_string e))) tl
     *   ; *)
    if keep_hd then
      hd::tl
    else
      tl
  )
  
let check_sat ?(just_check=false) (l:guard) : bool * guard =
  (* Syntactic simplification *)
  (* Format.eprintf "Before simplify: %a@." pp_guard_list l; *)
  let l = simplify_neg_guard l in
  (* Format.eprintf "After simplify: %a@." pp_guard_list l; *)
  (* Format.eprintf "@[<v 2>Z3 check sat: [%a]@ " pp_guard_list l; *)
  let solver = Z3.Solver.mk_simple_solver !ctx in
  try (
    let zl =
      List.map (fun (e, posneg) ->
          let ze =
            match e with
            | IsInit -> is_init_z3e
            | Expr e -> expr_to_z3_expr e 
          in
          if posneg then
            ze
          else
            neg_ze ze
        ) l
    in
    (* Format.eprintf "Z3 exprs1: [%a]@ " (fprintf_list ~sep:",@ " (fun fmt e -> Format.fprintf fmt "%s" (Z3.Expr.to_string e))) zl; *)
    let zl = simplify zl in
       (* Format.eprintf "Z3 exprs2: [%a]@ " (fprintf_list ~sep:",@ " (fun fmt e -> Format.fprintf fmt "%s" (Z3.Expr.to_string e))) zl; *)
    let status_res = Z3.Solver.check solver zl in
    (* Format.eprintf "Z3 status: %s@ @]@. " (Z3.Solver.string_of_status status_res); *)
    match status_res with
    | Z3.Solver.UNSATISFIABLE -> false, []
    | _ -> (
      if false && just_check then
        true, l
      else
        let zl = goal_simplify zl in
        let l = zexpr_to_guard_list zl in
  (* Format.eprintf "@.@[<v 2>Check_Sat:@ before: %a@ after:
       %a@. Goal precise? %b/%b@]@.@. " * pp_guard_list l
       pp_guard_list l' * (Z3.Goal.is_precise goal) *
       (Z3.Goal.is_precise goal'); *)
  

        true, l
        
         
    )
         
  )
  with Zustre_common.UnknownFunction(id, msg) -> (
    report ~level:1 msg;
    true, l (* keeping everything. *)
  )
      
  


(**************************************************************)

  
let clean_sys sys =
  List.fold_left (fun accu (guards, updates) ->
      (*let guards' = clean_guard guards in*)
      let sat, guards' =  check_sat (List.map (fun (g, pn) -> Expr g, pn) guards) in
      (*Format.eprintf "Guard: %a@.Guard cleaned: %a@.Sat? %b@."
        (fprintf_list ~sep:"@ " (pp_guard_expr Printers.pp_expr))  guards
        (fprintf_list ~sep:"@ " (pp_guard_expr Printers.pp_expr))  guards'
        sat

      ;*)
        if sat then
        (List.map (fun (e, b) -> (deelem e, b)) guards', updates)::accu
      else
        accu
    )
    [] sys
  
let combine_guards ?(fresh=None) gl1 gl2 =
  (* Filtering out trivial cases. More semantics ones would have to be
     addressed later *)
  let check (gexpr, posneg) l =
    (* Format.eprintf "Checking %a=%b in %a@ "
     *   pp_elem gexpr
     *   posneg
     *   pp_guard_list l
     * ; *)
    (* Check if gepxr is part of l *)
   let sel_fun = select_elem gexpr in
   let ok, res =
     if List.exists sel_fun l then (
      (* Checking the guard value posneg *)
      let _, status = List.find sel_fun l in
      (* Format.eprintf "Found %a in %a. @ Checking status (%b).@ "
     *     pp_elem gexpr
     *     pp_guard_list l
     *     (status=posneg)
     * ; *)
      status=posneg, l
    )
    else (
      (* Format.eprintf "Not found.@ "; *)
      (* Valid: no overlap *)
      (* Individual checkat *)
      let ok, e = check_sat ~just_check:true [gexpr, posneg] in
      (* let ok, e = true, [gexpr, posneg] in (* TODO solve the issue with check_sat *) *)
      (* Format.eprintf "Check_sat? %b@ " ok; *)
      if ok then
        let l = e@l in
        let ok, l = check_sat ~just_check:true l in
        (* let ok, l = true, l in (* TODO solve the issue with check_sat *) *)
        ok, l 
      else
        false, []
     )
   in
   (* Format.eprintf "Check sat res: %a@ "
    *   pp_guard_list res; *)
   ok, res
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
    false, []

(* DEBUG 
let combine_guards  ?(fresh=None) gl1 gl2 =
  true,
  (match fresh with None -> [] | Some (gexpr, posneg) -> [gexpr, posneg])@gl1@gl2
 *)
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
           (* Format.eprintf "@[<v 2>Combining guards: (%a=%b) AND [%a] AND [%a]@ "
            *  pp_elem e1
            *  posneg
            *  pp_guard_list g1
            *  pp_guard_list g2; *)
            
          let ok, gl = combine_guards ~fresh:(Some(e1,posneg)) g1 g2 in
          (* Format.eprintf "@]@ Result is [%a]@ "
           *   pp_guard_list gl; *)
            
          if ok then
            (gl, e2)::accu
          else (
            
            accu
          )
        ) accu gel1
    ) [] gel2

let rec rewrite defs expr : guarded_expr list =
  let rewrite = rewrite defs in
  let res =
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
  in
  (* Format.eprintf "Rewriting %a as [@[<v 0>%a@]]@ "
   *   Printers.pp_expr expr
   *   (Utils.fprintf_list ~sep:"@ "
   *        pp_guard_expr) res; *)
  res
and add_def defs vid expr =
  let vid_defs = rewrite defs expr in
  (* Format.eprintf "Add_def: %s = %a@. -> @[<v 0>%a@]@."
   *     vid
   *     Printers.pp_expr expr
   *     (
   *       (Utils.fprintf_list ~sep:"@ "
   *          pp_guard_expr)) vid_defs;  *)
  Hashtbl.add defs vid vid_defs

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
      (mem_defs: (ident * guarded_expr list) list)
      :
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

let pick_guard mem_defs : expr option =
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
  try
  Some (List.hd all_guards)  
  with _ -> None
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
     other mem, one need to select the same guard g with the same
     status b, *)
  if List.for_all (fun (m,mdefs) ->
         (* All defs are unguarded *)
         match mdefs with
         | [[], _] -> true
         | _ -> false
       ) mem_defs
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
    let elem_opt : expr option = pick_guard mem_defs in
    match elem_opt with
      None -> []
    | Some elem -> (
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
         let clean l =
           let l = List.map (fun (e,b) -> (Expr e), b) l in
           let ok, l = check_sat l in
           let l = List.map (fun (e,b) -> deelem e, b) l in
           ok, l
         in
         let pos_prefix = (elem, true)::prefix in
         let ok_pos, pos_prefix = clean pos_prefix in         
         let neg_prefix = (elem, false)::prefix in
         let ok_neg, neg_prefix = clean neg_prefix in         
         
         (if ok_pos then build_switch_sys pos pos_prefix else [])
         @
           (if ok_neg then build_switch_sys neg neg_prefix else [])
    )


      
(* Take a normalized node and extract a list of switches: (cond,
   update) meaning "if cond then update" where update shall define all
   node memories. Everything as to be expressed over inputs or memories, intermediate variables are removed through inlining *)
let node_as_switched_sys consts (mems:var_decl list) nd =
  (* rescheduling node: has been scheduled already, no need to protect
     the call to schedule_node *)
  let nd_report = Scheduling.schedule_node nd in
  let schedule = nd_report.Scheduling_type.schedule in
  let eqs, auts = Corelang.get_node_eqs nd in
  assert (auts = []); (* Automata should be expanded by now *)
  let sorted_eqs = Scheduling.sort_equations_from_schedule eqs schedule in
  let defs : (ident,  guarded_expr list) Hashtbl.t = Hashtbl.create 13 in
  let add_def = add_def defs in

  let vars = Corelang.get_node_vars nd in
  (* Registering all locals variables as Z3 predicates. Will be use to
     simplify the expansion *) 
  let _ =
    List.iter (fun v ->
        let fdecl = Z3.FuncDecl.mk_func_decl_s
                      !ctx
                      v.var_id
                      []
                      (Zustre_common.type_to_sort v.var_type)
        in
        ignore (Zustre_common.register_fdecl v.var_id fdecl)
      ) vars
  in
  let _ =
    List.iter (fun c -> Hashtbl.add const_defs c.const_id c.const_value) consts
  in

  
  (* Registering node equations: identifying mem definitions and
     storing others in the "defs" hashtbl. *)
  let mem_defs =
    List.fold_left (fun accu eq ->
        match eq.eq_lhs with
        | [vid] ->
           (* Only focus on non memory definitions *)
           if not (List.exists (fun v -> v.var_id = vid) mems) then (
             report ~level:3 (fun fmt ->
                 Format.fprintf fmt "Registering variable %s@." vid);
             add_def vid eq.eq_rhs;
             accu
           )
           else
             (
               match eq.eq_rhs.expr_desc with
               | Expr_pre def_m ->
                  report ~level:3 (fun fmt ->
                      Format.fprintf fmt "Preparing mem %s@." vid);
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
  (* Format.eprintf "Split init@."; *)
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
  (* Format.eprintf "Build init@."; *)

  let sw_init= 
    build_switch_sys init_defs []
  in
  (* Format.eprintf "Build step@."; *)
  let sw_sys =
    build_switch_sys update_defs []
  in
  clean_sys sw_init, clean_sys sw_sys
 
