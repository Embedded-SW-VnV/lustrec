open Lustre_types
open Utils
open Seal_utils			
open Zustre_data (* Access to Z3 context *)
   
  
(* Switched system extraction: expression are memoized *)
(*let expr_mem = Hashtbl.create 13*)
    
let add_init defs vid =
  Hashtbl.add defs vid [[], IsInit]


(**************************************************************)
(* Convert from Lustre expressions to Z3 expressions and back *)
(* All (free) variables have to be declared in the Z3 context *)
(**************************************************************)

let is_init_name = "__is_init"

let const_defs = Hashtbl.create 13
let is_const id = Hashtbl.mem const_defs id
let is_enum_const id = Hashtbl.mem Zustre_data.const_tags id  
let get_const id = Hashtbl.find const_defs id
                 
(* expressions are only basic constructs here, no more ite, tuples,
   arrows, fby, ... *)

(* Set of hash to support memoization *)
let expr_hash: (expr * Utils.tag) list ref = ref []
let ze_hash: (Z3.Expr.expr, Utils.tag) Hashtbl.t = Hashtbl.create 13
let e_hash: (Utils.tag, Z3.Expr.expr) Hashtbl.t = Hashtbl.create 13
let pp_hash pp_key pp_v fmt h = Hashtbl.iter (fun key v -> Format.fprintf fmt "%a -> %a@ " pp_key key pp_v v) h
let pp_e_map fmt = List.iter (fun (e,t) -> Format.fprintf fmt "%i -> %a@ " t Printers.pp_expr e) !expr_hash
let pp_ze_hash fmt = pp_hash
                      (fun fmt e -> Format.fprintf fmt "%s" (Z3.Expr.to_string e))
                      Format.pp_print_int
                      fmt
                      ze_hash
let pp_e_hash fmt = pp_hash
                      Format.pp_print_int
                      (fun fmt e -> Format.fprintf fmt "%s" (Z3.Expr.to_string e))
                      fmt
                      e_hash                              
let mem_expr e =
  (* Format.eprintf "Searching for %a in map: @[<v 0>%t@]"
   *   Printers.pp_expr e
   *   pp_e_map; *)
  let res = List.exists (fun (e',_) -> Corelang.is_eq_expr e e') !expr_hash in
  (* Format.eprintf "found?%b@." res; *)
  res
  
let mem_zexpr ze =
  Hashtbl.mem ze_hash ze
let get_zexpr e =
  let eref, uid = List.find (fun (e',_) -> Corelang.is_eq_expr e e') !expr_hash in
  (* Format.eprintf "found expr=%a id=%i@." Printers.pp_expr eref eref.expr_tag; *)
  Hashtbl.find e_hash uid
let get_expr ze =
  let uid = Hashtbl.find ze_hash ze in
  let e,_ = List.find (fun (e,t) -> t = uid) !expr_hash in
  e
  
let neg_ze z3e = Z3.Boolean.mk_not !ctx z3e 
let is_init_z3e =
  Z3.Expr.mk_const_s !ctx is_init_name  Zustre_common.bool_sort 

let get_zid (ze:Z3.Expr.expr) : Utils.tag = 
  try
    if Z3.Expr.equal ze is_init_z3e then -1 else
      if Z3.Expr.equal ze (neg_ze is_init_z3e) then -2 else
    Hashtbl.find ze_hash ze
  with _ -> (Format.eprintf "Looking for ze %s in Hash %a"
               (Z3.Expr.to_string ze)
               (fun fmt hash -> Hashtbl.iter (fun ze uid -> Format.fprintf fmt "%s -> %i@ " (Z3.Expr.to_string ze) uid) hash ) ze_hash;
             assert false)
let add_expr =
  let cpt = ref 0 in
  fun e ze ->
  incr cpt;
  let uid = !cpt in
  expr_hash := (e, uid)::!expr_hash;
  Hashtbl.add e_hash uid ze;
  Hashtbl.add ze_hash ze uid

  
let expr_to_z3_expr, zexpr_to_expr =
  (* List to store converted expression. *)
  (* let hash = ref [] in
   * let comp_expr e (e', _) = Corelang.is_eq_expr e e' in
   * let comp_zexpr ze (_, ze') = Z3.Expr.equal ze ze' in *)
  
  let rec e2ze e =
    (* Format.eprintf "e2ze %a: %a@." Printers.pp_expr e Types.print_ty e.expr_type; *)
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
          else if is_enum_const id then (
            let z3e = Zustre_common.horn_tag_to_expr id in
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
           let el = Corelang.expr_list_of_expr args in
           
           let eltyp = List.map (fun e -> e.expr_type) el in
           let elv = List.map e2ze el in
           let z3e = Zustre_common.horn_basic_app id elv (eltyp, e.expr_type) in
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
              let s = Z3.Arithmetic.Real.numeral_to_string ze in
              (* Use to return a Num.ratio. Now Q.t *)
              let ratio = Z3.Arithmetic.Real.get_ratio ze in
              (*let num =  Num.num_of_ratio ratio in
              let real = Real.create_num num s in*)
              let real = Real.create_q ratio s in
              mkexpr
                Location.dummy_loc
                (Expr_const
                   (Const_real real))
            else if Z3.Arithmetic.is_int ze then
              mkexpr
                Location.dummy_loc
                (Expr_const
                   (Const_int 
                      (Z.to_int (Z3.Arithmetic.Integer.get_big_int ze))))
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
(*
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
  zexpr_to_guard_list ze
  *)
  
let implies =
  let ze_implies_hash : ((Utils.tag * Utils.tag), bool) Hashtbl.t  = Hashtbl.create 13 in
  fun ze1 ze2 ->
  let ze1_uid = get_zid ze1 in
  let ze2_uid = get_zid ze2 in
  if Hashtbl.mem ze_implies_hash (ze1_uid, ze2_uid) then
    Hashtbl.find ze_implies_hash (ze1_uid, ze2_uid)
  else
    begin
      if !seal_debug then (
        report ~level:6 (fun fmt -> Format.fprintf fmt "Checking implication: %s => %s?@ "
          (Z3.Expr.to_string ze1) (Z3.Expr.to_string ze2)
      )); 
      let solver = Z3.Solver.mk_simple_solver !ctx in
      let tgt = Z3.Boolean.mk_not !ctx (Z3.Boolean.mk_implies !ctx ze1 ze2) in
      let res =
        try
          let status_res = Z3.Solver.check solver [tgt] in
          match status_res with
          | Z3.Solver.UNSATISFIABLE -> if !seal_debug then
                                         report ~level:6 (fun fmt -> Format.fprintf fmt "Valid!@ "); 
             true
          | _ -> if !seal_debug then report ~level:6 (fun fmt -> Format.fprintf fmt "not proved valid@ "); 
             false
        with Zustre_common.UnknownFunction(id, msg) -> (
          report ~level:1 msg;
          false
        )
      in
      Hashtbl.add ze_implies_hash (ze1_uid,ze2_uid) res ;
      res
    end
                                               
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
  
let check_sat ?(just_check=false) (l: elem_boolexpr guard) : bool * (elem_boolexpr guard) =
  (* Syntactic simplification *)
  if false then
    Format.eprintf "Before simplify: %a@." (pp_guard_list pp_elem) l; 
  let l = simplify_neg_guard l in
  if false then (
    Format.eprintf "After simplify: %a@." (pp_guard_list pp_elem) l; 
    Format.eprintf "@[<v 2>Z3 check sat: [%a]@ " (pp_guard_list pp_elem)l;
  );
  
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
    if false then Format.eprintf "Z3 exprs1: [%a]@ " (fprintf_list ~sep:",@ " (fun fmt e -> Format.fprintf fmt "%s" (Z3.Expr.to_string e))) zl; 
    let zl = simplify zl in
    if false then Format.eprintf "Z3 exprs2: [%a]@ " (fprintf_list ~sep:",@ " (fun fmt e -> Format.fprintf fmt "%s" (Z3.Expr.to_string e))) zl; 
    (* Format.eprintf "Calling Z3@."; *)
    let status_res = Z3.Solver.check solver zl in
    (* Format.eprintf "Z3 done@."; *)
     if false then Format.eprintf "Z3 status: %s@ @]@. " (Z3.Solver.string_of_status status_res); 
    match status_res with
    | Z3.Solver.UNSATISFIABLE -> false, []
    | _ -> (
      if false && just_check then
        true, l
      else
        (* TODO: may be reactivate but it may create new expressions *)
        (* let l = goal_simplify zl in *)
        let l = List.fold_left
                  (fun accu ze -> accu @ (zexpr_to_guard_list ze))
                  []
                  zl
        in
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

(* Most costly function: has the be efficiently implemented.  All
   registered guards are initially produced by the call to
   combine_guards. We csan normalize the guards to ease the
   comparisons.

   We assume that gl1 and gl2 are already both satisfiable and in a
   kind of reduced form. Let lshort and llong be the short and long
   list of gl1, gl2. We check whether each element elong of llong is
   satisfiable with lshort. If no, stop. If yes, we search to reduce
   the list. If elong => eshort_i, we can remove eshort_i from
   lshort. we can continue with this lshort shortened, lshort'; it is
   not necessary to add yet elong in lshort' since we already know
   rthat elong is somehow reduced with respect to other elements of
   llong. If eshort_i => elong, then we keep ehosrt_i in lshort and do
   not store elong.

   After iterating through llong, we have a shortened version of
   lshort + some elements of llong that have to be remembered. We add
   them to this new consolidated list. 

 *)

(* combine_guards ~fresh:Some(e,b) gl1 gl2 returns ok, gl with ok=true
   when (e=b) ang gl1 and gl2 is satisfiable and gl is a consilidated
   version of it.  *)
let combine_guards ?(fresh=None) gl1 gl2 =
  (* Filtering out trivial cases. More semantics ones would have to be
     addressed later *)
  let check_sat e = (* temp function before we clean the original one *)
    (* Format.eprintf "CheckSAT? %a@." (pp_guard_list pp_elem) e; *)
    let ok, _ = check_sat e in
    (* Format.eprintf "CheckSAT DONE@."; *)
    ok
  in
  let implies (e1,pn1) (e2,pn2) =
    let e2z e pn =
      match e with
        | IsInit -> if pn then is_init_z3e else neg_ze is_init_z3e
        | Expr e -> expr_to_z3_expr (if pn then e else (Corelang.push_negations ~neg:true e))
      in
    implies (e2z e1 pn1) (e2z e2 pn2)
  in
  let lshort, llong =
    if List.length gl1 > List.length gl2 then gl2, gl1 else gl1, gl2
  in
  let merge long short =
    let short, long_sel, ok = 
    List.fold_left (fun (short,long_sel, ok) long_e ->
        if not ok then
          [],[], false (* Propagating unsat case *)
        else if check_sat (long_e::short) then
          let short, keep_long_e =
            List.fold_left (fun (accu_short, keep_long_e) eshort_i ->
                if not keep_long_e then (* shorten the algo *)
                  eshort_i :: accu_short, false
                else (* keep_long_e = true in the following *)
                  if implies eshort_i long_e then
                    (* First case is trying to remove long_e!

                     Since short is already normalized, we can remove
                     long_e. If later long_e is stronger than another
                     element of short, then necessarily eshort_i =>
                     long_e ->
                     that_other_element_of_short. Contradiction. *)
                    eshort_i::accu_short, false
                  else if implies long_e eshort_i then 
                    (* removing eshort_i, keeping long_e. *)
                    accu_short, true
                  else (* Not comparable, keeping both *)
                    eshort_i::accu_short, true
              )
              ([],true) (* Initially we assume that we will keep long_e *)
              short
          in
          if keep_long_e then
            short, long_e::long_sel, true
          else
            short, long_sel, true
        else
          [],[],false
      ) (short, [], true) long
    in
    ok, long_sel@short
  in
  let ok, l = match fresh with
    | None -> true, []
    | Some g -> merge [g] []
  in
  if not ok then
    false, []
  else
    let ok, lshort = merge lshort l in
    if not ok then
      false, []
    else
      merge llong lshort
    

(* Encode "If gel1=posneg then gel2":
   - Compute the combination of guarded exprs in gel1 and gel2:
     - Each guarded_expr in gel1 is transformed as a guard: the
       expression is associated to posneg.
     - Existing guards in gel2 are concatenated to that list of guards
     - We keep expr in the ge of gel2 as the legitimate expression 
 *)
let concatenate_ge gel1 posneg gel2 =
  let l, all_invalid =
    List.fold_left (
        fun (accu, all_invalid) (g2,e2) ->
        List.fold_left (
            fun (accu, all_invalid) (g1,e1) ->
            (* Format.eprintf "@[<v 2>Combining guards: (%a=%b) AND [%a] AND [%a]@ "
             *  pp_elem e1
             *  posneg
             *  pp_guard_list g1
             *  pp_guard_list g2; *)

            let ok, gl = combine_guards ~fresh:(Some(e1,posneg)) g1 g2 in
            (* Format.eprintf "@]@ Result is [%a]@ "
             *   pp_guard_list gl; *)

            if ok then
              (gl, e2)::accu, false
            else (
              accu, all_invalid
            )
          ) (accu, all_invalid) gel1
      ) ([], true) gel2
  in
  not all_invalid, l

(* Transform the guard expressions ge = [gl1, e1; gl2, e2;...] as
   [gl1, e1=id; gl2, e2=id; ...]  *)
let mk_ge_eq_id ge id =
  List.map
    (fun (gl, g_e) ->
      gl,
      if id = "true" then
        g_e
      else
        match g_e with
        | Expr g_e ->
           if id = "false" then
             Expr (Corelang.push_negations ~neg:true g_e)
           else  
             let loc = g_e.expr_loc in
             Expr(Corelang.mk_eq loc
                    g_e
                    (Corelang.expr_of_ident id loc))
        | _ -> assert false
    )  ge 

    (* Rewrite the expression expr, replacing any occurence of a variable
   by its definition.
     *)
let rec rewrite defs expr : elem_guarded_expr list =   
  let rewrite = rewrite defs in
  let res =
    match expr.expr_desc with
    | Expr_appl (id, args, None) ->
       let args = rewrite args in
       List.map (fun (guards, e) ->
       let new_e =
         Corelang.mkexpr
           expr.expr_loc
           (Expr_appl(id, deelem e, None))
       in
       let new_e = { new_e with expr_type = expr.expr_type; expr_clock = expr.expr_clock } in
       guards,
       Expr (Corelang.partial_eval new_e) 
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
       let ok_then, g_then = concatenate_ge g true e1 in
       let ok_else, g_else = concatenate_ge g false e2 in
       (if ok_then then g_then else [])@
         (if ok_else then g_else else [])
    | Expr_merge (g_id, branches) ->
       if Hashtbl.mem defs g_id then
         let g = Hashtbl.find defs g_id in
         (* Format.eprintf "Expr_merge %s = %a@." g_id (pp_mdefs pp_elem) g ; *)
         List.fold_left (fun accu (id, e) ->
             let g = mk_ge_eq_id g id in
             let e = rewrite e in
             let ok, g_eq_id = concatenate_ge g true e in
             if ok then g_eq_id@accu else accu
           ) [] branches
       else
         assert false (* g should be defined already *)
    | Expr_when (e, id, l) ->
       let e = rewrite e in
       let id_def = Hashtbl.find defs id in
       let clock = mk_ge_eq_id id_def l in
       let ok, new_ge = concatenate_ge clock true e in
       if ok then new_ge else []
    | Expr_arrow _ -> [[], IsInit] (* At this point the only arrow should be true -> false *)
    | Expr_tuple el ->
       (* Each expr is associated to its flatten guarded expr list *)
       let gell = List.map rewrite el in
       (* Computing all combinations: we obtain a list of guarded tuple *)
       let rec aux gell : (elem_boolexpr guard * expr list) list =
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
                      let new_gt : elem_boolexpr guard * expr list =
                        (guard_comb, (deelem e)::minituple) in
                      new_gt::accu
                    else
                      accu
                    
                  ) accu getl
              ) [] gel
       in
       let gtuples = aux gell in
       (* Rebuilding the valid type: guarded expr list (with tuple exprs) *)
       List.map
         (fun (g,tuple) -> g, Expr (Corelang.mkexpr expr.expr_loc (Expr_tuple tuple)))
         gtuples
    | Expr_fby _
      | Expr_appl _
                  (* Should be removed by normalization and inlining *)
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
   *        (pp_guard_expr pp_elem)) res; *)
  res
  
and add_def defs vid expr =
  (* Format.eprintf "Add_def: %s = %a@."
   *   vid
   *   Printers.pp_expr expr; *)
  let vid_defs = rewrite defs expr in
  (* Format.eprintf "-> @[<v 0>%a@]@."
   *   (Utils.fprintf_list ~sep:"@ "
   *      (pp_guard_expr pp_elem)) vid_defs; *)
  report ~level:6 (fun fmt -> Format.fprintf fmt  "Add_def: %s = %a@. -> @[<v 0>%a@]@."
      vid
      Printers.pp_expr expr
      
      (
        (Utils.fprintf_list ~sep:"@ "
           (pp_guard_expr pp_elem))) vid_defs);
  Hashtbl.add defs vid vid_defs;
  vid_defs

(* Takes a list of guarded exprs (ge) and a guard
returns the same list of ge splited into the ones where the guard is true and the ones where it is false. In both lists the associated ge do not mention that guard anymore.

When a given ge doesn't mention positively or negatively such guards, it is duplicated in both lists *)
let split_mdefs elem (mdefs: elem_guarded_expr list) =
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
          (pp_mdefs pp_elem) mdefs;
        assert false (* more then one element selected. Should
                          not happen , or trival dead code like if
                              x then if not x then dead code *)
      )
    ) ([],[]) mdefs
    
let split_mem_defs
      (elem: element)
      (mem_defs: (ident * elem_guarded_expr list) list)
      :
      ((ident * elem_guarded_expr mdef_t) list) * ((ident * elem_guarded_expr mdef_t) list)
  
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

(* Previous version of the function: way too costly 
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
   *)

(* Returning the first non empty guard expression *)
let rec pick_guard mem_defs : expr option =
  match mem_defs with
  | [] -> None
  | (_, gel)::tl -> (
    let found =
      List.fold_left (fun found (g,_) ->
          if found = None then
            match g with
            | [] -> None
            | (Expr e, _)::_ -> Some e
            | (IsInit, _)::_ -> assert false (* should be removed already *)
          else
            found
        ) None gel
    in
    if found = None then pick_guard tl else found
  )
          

(* Transform a list of variable * guarded exprs into a list of guarded pairs (variable, expressions)
*)
let rec build_switch_sys
          (mem_defs : (Utils.ident * elem_guarded_expr list) list )
          prefix
        :
          ((expr * bool) list * (ident * expr) list ) list =
  if !seal_debug then
    report ~level:4 (fun fmt -> Format.fprintf fmt "@[<v 2>Build_switch with@ %a@]@."
                                  pp_all_defs
                                  mem_defs);
  (* if all mem_defs have empty guards, we are done, return prefix,
     mem_defs expr.

     otherwise pick a guard in one of the mem, eg (g, b) then for each
     other mem, one need to select the same guard g with the same
     status b, *)
  let res =
  if List.for_all (fun (m,mdefs) ->
         (* All defs are unguarded *)
         match mdefs with
         | [[], _] -> true (* Regular unguarded expression *)
         | [] -> true (* A unbalanced definition of the memory. Here
                         we have m_{k+1} -> m_k *)
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
         | [] -> m, Corelang.expr_of_ident m Location.dummy_loc
         | _ -> assert false
       ) mem_defs]
  else
    (* Picking a guard *)
    let elem_opt : expr option = pick_guard mem_defs in
    match elem_opt with
      None -> (
       Format.eprintf "Issues picking guard in mem_defs: %a@." pp_all_defs mem_defs;
       assert false (* Otherwise the first case should have matched *)
    )
    | Some elem -> (
      report ~level:4 (fun fmt -> Format.fprintf fmt "selecting guard %a@." Printers.pp_expr elem);
      let pos, neg =
        split_mem_defs
          (Expr elem)
          mem_defs
      in
      report ~level:4 (fun fmt -> Format.fprintf fmt "split by guard done@.");
      
  (*    Format.eprintf "Selected item %a in@.%a@.POS=%a@.NEG=%a@."
        Printers.pp_expr elem
        pp_all_defs mem_defs
        pp_all_defs pos
        pp_all_defs neg
        ;
   *)
      (* Special cases to avoid useless computations: true, false conditions *)
      match elem.expr_desc with
      (*| Expr_ident "true"  ->   build_switch_sys pos prefix *)
      | Expr_const (Const_tag tag) when tag = tag_true
        ->   build_switch_sys pos prefix
      (*| Expr_ident "false" ->   build_switch_sys neg prefix *)
      | Expr_const (Const_tag tag) when tag = tag_false 
        ->   build_switch_sys neg prefix
      | _ -> (* Regular case *)
         report ~level:4 (fun fmt -> Format.fprintf fmt "Building both children branches@."); 
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
           report ~level:4 (fun fmt -> Format.fprintf fmt "Checking satisfiability of %a@."
                                     (pp_guard_list pp_elem) l
             );
           let ok, l = check_sat l in
           let l = List.map (fun (e,b) -> deelem e, b) l in
           ok, l
         in
         let pos_prefix = (elem, true)::prefix in
         let neg_prefix = (elem, false)::prefix in
         report ~level:4 (fun fmt -> Format.fprintf fmt "Cleaning branches ...@."); 
         let ok_pos, pos_prefix = clean pos_prefix in         
         report ~level:4 (fun fmt -> Format.fprintf fmt "Cleaning branche pos done@."); 
         let ok_neg, neg_prefix = clean neg_prefix in
         report ~level:4 (fun fmt -> Format.fprintf fmt "Cleaning branche neg done@."); 
         report ~level:4 (fun fmt -> Format.fprintf fmt "Cleaning branches done@."); 
         report ~level:4 (fun fmt -> Format.fprintf fmt "Enforcing %a@." Printers.pp_expr elem);
         let ok_l = if ok_pos then build_switch_sys pos pos_prefix else [] in
         report ~level:4 (fun fmt -> Format.fprintf fmt "Enforcing not(%a)@." Printers.pp_expr elem);
         let nok_l = if ok_neg then build_switch_sys neg neg_prefix else [] in
         ok_l @ nok_l
    )
  in
    if !seal_debug then (
      report ~level:4 (fun fmt ->
          Format.fprintf fmt
            "@[<v 2>===> @[%t@ @]@]@ @]@ "
            (fun fmt -> List.iter (fun (gl,up) ->
                            Format.fprintf fmt "[@[%a@]] -> (%a)@ "
                              (pp_guard_list Printers.pp_expr) gl (pp_up Printers.pp_expr) up) res);
          
    ));
    res
  

let build_environement  consts (mems:var_decl list) nd =
    
  Z3.Params.update_param_value !ctx "timeout" "10000";

 
  (* rescheduling node: has been scheduled already, no need to protect
     the call to schedule_node *)
  let nd_report = Scheduling.schedule_node nd in
  let schedule = nd_report.Scheduling_type.schedule in
  let eqs, auts = Corelang.get_node_eqs nd in
  assert (auts = []); (* Automata should be expanded by now *)
  let sorted_eqs, unused = Scheduling.sort_equations_from_schedule eqs schedule in
  let defs : (ident,  elem_guarded_expr list) Hashtbl.t = Hashtbl.create 13 in
  let add_def = add_def defs in

  let vars = Corelang.get_node_vars nd in
  (* Filtering out unused vars *)
  let vars = List.filter (fun v -> not (List.mem v.var_id unused)) vars in
  (* Registering all locals variables as Z3 predicates. Will be use to
     simplify the expansion *)
  Zustre_common.decl_sorts (); 
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

  report ~level:4 (fun fmt -> Format.fprintf fmt "Computing definitions for equations@.%a@."
                            Printers.pp_node_eqs sorted_eqs
    );
  
  
  (* Registering node equations: identifying mem definitions and
     storing others in the "defs" hashtbl.

     Each assign is stored in a hash tbl as list of guarded
     expressions. The memory definition is also "rewritten" as such a
     list of guarded assigns.  *)
  report ~level:1 (fun fmt -> Format.fprintf fmt "registering all definitions in guarded form ...@.");
  let mem_defs, output_defs =
    List.fold_left (fun (accu_mems, accu_outputs) eq ->
        match eq.eq_lhs with
        | [vid] ->
           (* Only focus on memory definitions *)
           if List.exists (fun v -> v.var_id = vid) mems then 
             (
               match eq.eq_rhs.expr_desc with
               | Expr_pre def_m ->
                  report ~level:3 (fun fmt ->
                      Format.fprintf fmt "Preparing mem %s@." vid);
                  let def_vid = rewrite defs def_m in
                  report ~level:4 (fun fmt ->
                      Format.fprintf fmt "%s = %a@." vid
 (
        (Utils.fprintf_list ~sep:"@ "
           (pp_guard_expr pp_elem))) 
                        def_vid);
                  (vid, def_vid)::accu_mems, accu_outputs
               | _ -> assert false
             ) 
           else if List.exists (fun v -> v.var_id = vid) nd.node_outputs then (
             report ~level:3 (fun fmt ->
                 Format.fprintf fmt "Output variable %s@." vid);
             let def_vid = add_def vid eq.eq_rhs in
             accu_mems, (vid, def_vid)::accu_outputs
             
           )
           else
             (
               report ~level:3 (fun fmt ->
                   Format.fprintf fmt "Registering variable %s@." vid);
               let _ = add_def vid eq.eq_rhs in
               accu_mems, accu_outputs
             )
        | _ -> assert false (* should have been removed by normalization *)
      ) ([], []) sorted_eqs
  in
  report ~level:1 (fun fmt -> Format.fprintf fmt "registering all definitions done@.");

  
  report ~level:2 (fun fmt -> Format.fprintf fmt "Printing out (guarded) memories definitions (may takes time)@.");
  (* Printing memories definitions *)
  report ~level:3
    (fun fmt ->
      Format.fprintf fmt
        "@[<v 0>%a@]@."
        (Utils.fprintf_list ~sep:"@ "
           (fun fmt (m,mdefs) ->
             Format.fprintf fmt
               "%s -> [@[<v 0>%a@] ]@ "
               m
               (Utils.fprintf_list ~sep:"@ "
                  (pp_guard_expr pp_elem)) mdefs
        ))
        mem_defs);
  mem_defs, output_defs 


(* Iter through the elements and gather them by updates *)
let merge_updates sys =
  (* The map will associate to each update up the pair (set, set
       list) where set is the share guards and set list a list of
       disjunctive guards. Each set represents a conjunction of
       expressions. *)
  
  (* We perform multiple pass to avoid errors *)
  let map =
    List.fold_left (fun map (gl,up) ->
        (* creating a new set to describe gl *)
        let new_set =
          List.fold_left
            (fun set g -> Guards.add g set)
            Guards.empty
            gl
        in
        (* updating the map with up -> new_set *)
        if UpMap.mem up map then
          let guard_set = UpMap.find up map in
          UpMap.add up (new_set::guard_set) map
        else
          UpMap.add up [new_set] map
      ) UpMap.empty sys
  in

  (* Processing the set of guards leading to the same update: return
       conj, disj with conf is a set of guards, and disj a DNF, ie a
       list of set of guards *)
  let map =
    UpMap.map (
        fun guards ->
        match guards with
        | [] -> Guards.empty, [] (* Nothing *)
        | [s]-> s, [] (* basic case *)
        | hd::tl ->
           let shared = List.fold_left (fun shared s -> Guards.inter shared s) hd tl in
           let remaining = List.map (fun s -> Guards.diff s shared) guards in
           (* If one of them is empty, we can remove the others, otherwise keep them *)
           if List.exists Guards.is_empty remaining then
             shared, []
           else
             shared, remaining
      ) map
  in
  let rec mk_binop op l = match l with
      [] -> assert false
    | [e] -> e
    | hd::tl -> Corelang.mkpredef_call hd.expr_loc op [hd; mk_binop op tl]
  in
  let gl_as_expr gl =
    let gl = Guards.elements gl in
    let export (e,b) = if b then e else Corelang.push_negations ~neg:true e in 
    match gl with
      [] -> []
    | [e] -> [export e]
    | _ ->
       [mk_binop "&&"
          (List.map export gl)]
  in
  let rec clean_disj disj =
    match disj with
    | [] -> []
    | [_] -> assert false (* A disjunction with a single case can be ignored *) 
    | _::_::_ -> (
      (* First basic version: producing a DNF One can later, (1)
           simplify it with z3, or (2) build the compact tree with
           maximum shared subexpression (and simplify it with z3) *)
      let elems = List.fold_left (fun accu gl -> (gl_as_expr gl) @ accu) [] disj in
      let or_expr = mk_binop "||" elems in
      [or_expr]


    (* TODO disj*)
    (* get the item that occurs in most case *)
    (* List.fold_left (fun accu s ->
     *     List.fold_left (fun accu (e,b) ->
     *         if List.mem_assoc (e.expr_tag, b)
     *       ) accu (Guards.elements s)
     *   ) [] disj *)

    )
  in
  if !seal_debug then Format.eprintf "Map: %i elements@ " (UpMap.cardinal map);
  UpMap.fold (fun up (common, disj) accu ->
      if !seal_debug then
        report ~level:6 (fun fmt -> Format.fprintf fmt 
                                      "Guards:@.shared: [%a]@.disj: [@[<v 0>%a@ ]@]@.Updates: %a@."
                                      Guards.pp_short common
                                      (fprintf_list ~sep:";@ " Guards.pp_long) disj
                                      UpMap.pp up);
      let disj = clean_disj disj in
      let guard_expr = (gl_as_expr common)@disj in
      
      ((match guard_expr with
        | [] -> None 
        | _ -> Some (mk_binop "&&" guard_expr)), up)::accu
    ) map []
  
    
    

(* Take a normalized node and extract a list of switches: (cond,
   update) meaning "if cond then update" where update shall define all
   node memories. Everything as to be expressed over inputs or
   memories, intermediate variables are removed through inlining *)
let node_as_switched_sys consts (mems:var_decl list) nd =
  let mem_defs, output_defs = build_environement consts mems nd in
  
  let init_defs, update_defs = split_init mem_defs in
  let init_out, update_out =   split_init output_defs in
  
  report ~level:3 (fun fmt -> Format.fprintf fmt "@[<v 0>Init:@ %a@ Step:@ %a@]@."
                                (pp_assign_map pp_elem) init_defs
                                (pp_assign_map pp_elem) update_defs);
  

  report ~level:1 (fun fmt -> Format.fprintf fmt
                                "init/step as a switched system ...@.");
  let sw_init= build_switch_sys init_defs [] in
  let sw_sys = build_switch_sys update_defs [] in
  report ~level:1 (fun fmt -> Format.fprintf fmt
                                "init/step as a switched system ... done@.");


  report ~level:1 (fun fmt -> Format.fprintf fmt
                                "output function as a switched system ...@.");
  let init_out =   build_switch_sys init_out [] in
  let update_out = build_switch_sys update_out [] in
  
  report ~level:1 (fun fmt -> Format.fprintf fmt
                                "output function as a switched system ... done@.");

  report ~level:1 (fun fmt -> Format.fprintf fmt
                                "removing dead branches and merging remaining ...@.");

  let sw_init = clean_sys sw_init in
  let sw_sys = clean_sys sw_sys in
  let init_out = clean_sys init_out in
  let update_out = clean_sys update_out in

  report ~level:3 (fun fmt -> Format.fprintf fmt "Process sw_init:@.");
  let sw_init = merge_updates sw_init in
  report ~level:3 (fun fmt -> Format.fprintf fmt "Process sw_sys:@.");
  let sw_sys = merge_updates sw_sys in
  report ~level:3 (fun fmt -> Format.fprintf fmt "Process init_out:@.");
  let init_out = merge_updates init_out in
  report ~level:3 (fun fmt -> Format.fprintf fmt "Process update_out:@.");
  let update_out = merge_updates update_out in
  report ~level:1 (fun fmt ->
      Format.fprintf fmt "removing dead branches and merging remaining ... done@.");

  sw_init , sw_sys, init_out, update_out


let fun_as_switched_sys consts  nd =
  let _, update_out = build_environement consts [] nd in

  report ~level:1 (fun fmt -> Format.fprintf fmt
                                "output function as a switched system ...@.");
  let update_out = build_switch_sys update_out [] in
  report ~level:1 (fun fmt -> Format.fprintf fmt
                                "output function as a switched system ... done@.");

  report ~level:1 (fun fmt -> Format.fprintf fmt
                                "removing dead branches and merging remaining ...@.");
  let update_out = clean_sys update_out in
  let update_out = merge_updates update_out in
  report ~level:1 (fun fmt ->
      Format.fprintf fmt "removing dead branches and merging remaining ... done@.");

  update_out




                                
                                (* Some code that was used to check for duplicate entries in guards.


  (* Some additional checks *)
  
  if false then
    begin
      Format.eprintf "@.@.CHECKING!!!!!!!!!!!@.";
      Format.eprintf "Any duplicate expression in guards?@.";
      
      let sw_sys =
        List.map (fun (gl, up) ->
            let gl = List.sort (fun (e,b) (e',b') ->
                         let res = compare e.expr_tag e'.expr_tag in
                         if res = 0 then (Format.eprintf "Same exprs?@.%a@.%a@.@."
                                            Printers.pp_expr e
                                            Printers.pp_expr e'
                                         );
                         res
                       ) gl in
            gl, up
          ) sw_sys 
      in
      Format.eprintf "Another check for duplicates in guard list@.";
      List.iter (fun (gl, _) ->
          let rec aux hd l =
            match l with
              [] -> ()
            | (e,b)::tl -> let others = hd@tl in
                           List.iter (fun (e',_) -> if Corelang.is_eq_expr e e' then
                                                      (Format.eprintf "Same exprs?@.%a@.%a@.@."
                                                         Printers.pp_expr e
                                                         Printers.pp_expr e'
                             )) others;
                           aux ((e,b)::hd) tl
          in
          aux [] gl
        ) sw_sys;
      Format.eprintf "Checking duplicates in updates@.";
      let rec check_dup_up accu l =
        match l with
        | [] -> ()
        | ((gl, up) as hd)::tl ->
           let others = accu@tl in
           List.iter (fun (gl',up') -> if up = up' then
                                         Format.eprintf "Same updates?@.%a@.%a@.%a@.%a@.@."

                                           pp_gl_short gl
                                           pp_up up
                                           pp_gl_short gl'
                                           pp_up up'
                                       
             ) others;
           
           

           check_dup_up (hd::accu) tl
           
      in
      check_dup_up [] sw_sys;
      let _ (* sw_sys *) =
        List.sort (fun (gl1, _) (gl2, _) ->
            let glid gl = List.map (fun (e,_) -> e.expr_tag) gl in
            
            let res = compare (glid gl1) (glid gl2) in
            if res = 0 then Format.eprintf "Same guards?@.%a@.%a@.@."
                              pp_gl_short gl1 pp_gl_short gl2
            ;
              res

          ) sw_sys

      in
      ()
    end;
  

                                 *)
