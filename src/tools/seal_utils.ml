open Lustre_types
open Utils
   
let report = Log.report ~plugin:"seal"
           
let compute_sliced_vars vars_to_keep deps nd =
  let is_variable vid = 
    List.exists
      (fun v -> v.var_id = vid)
      nd.node_locals
  in
  let find_variable vid = 
    List.find
      (fun v -> v.var_id = vid)
      nd.node_locals
  in  

  (* Returns the vars required to compute v. 
     Memories are specifically identified. *)
  let coi_var v =
    let vname = v.var_id in
    let sliced_deps =
      Causality.slice_graph deps vname
    in
    (* Format.eprintf "sliced graph for %a: %a@."
     *   Printers.pp_var v
     *   Causality.pp_dep_graph sliced_deps; *)
    let vset, memset =
      IdentDepGraph.fold_vertex
        (fun vname (vset,memset)  ->
          if Causality.ExprDep.is_read_var vname
          then
            let vname' = String.sub vname 1 (-1 + String.length vname) in
            if is_variable vname' then
              ISet.add vname' vset,
              ISet.add vname' memset
            else
              vset, memset
          else
            ISet.add vname vset, memset
        )
        sliced_deps
        (ISet.singleton vname, ISet.empty)
    in
    report ~level:3 (fun fmt -> Format.fprintf fmt "COI of var %s: (%a // %a)@."
                                    v.var_id
                                    (fprintf_list ~sep:"," Format.pp_print_string) (ISet.elements vset)
                                    (fprintf_list ~sep:"," Format.pp_print_string) (ISet.elements memset)
      )  ;
    vset, memset
  in

  (* Computes the variables required to compute
     vl. Variables /seen/ do not need to 
     be computed *) 
  let rec coi_vars vl seen = 
    List.fold_left
      (fun accu v ->
        let vset, memset = coi_var v in
        (* We handle the new mems 
           discovered in  the coi *)
        let memset =
          ISet.filter (
              fun vid ->
              not
                (List.exists
                   (fun v -> v.var_id = vid)
                   vl
                ) 
            ) memset
        in
        let memset_vars = 
          ISet.fold (
              fun vid accu ->
              (find_variable vid)::accu
            ) memset [] 
        in
        let vset' =
          coi_vars memset_vars (vl@seen)
        in
        ISet.union accu (ISet.union vset vset')
      )
      ISet.empty
      (List.filter
         (fun v -> not (List.mem v seen))
         vl
      )
  in
  ISet.elements (coi_vars vars_to_keep []) 


  (* If existing outputs are included in vars_to_keep, just slice the content.
   Otherwise outputs are replaced by vars_to_keep *)
let slice_node vars_to_keep msch nd =
  let coi_vars =
    compute_sliced_vars vars_to_keep msch.Scheduling_type.dep_graph nd
  in
  report ~level:3 (fun fmt -> Format.fprintf fmt
                                  "COI Vars: %a@."
    (Utils.fprintf_list ~sep:"," Format.pp_print_string)
     coi_vars);
  let outputs =
    List.filter
      (
        fun v -> List.mem v.var_id coi_vars 
      ) nd.node_outputs
  in
  let outputs = match outputs with
      [] -> (
      report ~level:1 (fun fmt -> Format.fprintf fmt "No visible output variable, subtituting with provided vars@ ");
      vars_to_keep
    )
    | l -> l
  in
  let locals =
    List.filter (fun v -> List.mem v.var_id coi_vars) nd.node_locals
  in

  (* Split tuples while sorting eqs *)
  let sorted_eqs = Scheduling.sort_equations_from_schedule nd msch.Scheduling_type.schedule in

  let stmts =
    List.filter (
        fun (* stmt ->
         * match stmt with
         * | Aut _ -> assert false
         * | Eq *) eq -> (
          match eq.eq_lhs with
            [vid] -> List.mem vid coi_vars
          | _ -> Format.eprintf "Faulty statement: %a@.@?" Printers.pp_node_eq eq; assert false
        (* should not happen after inlining and normalization *)
        )
      ) sorted_eqs
  in
  { nd
  with
    node_outputs = outputs;
    node_locals = locals;
    node_stmts = List.map (fun e -> Eq e) stmts 
  } 

(* Switched system extraction *)
type element = IsInit | Expr of expr
type guarded_expr = (element * bool) list * element
type mdef_t = guarded_expr list
            
let pp_guard_expr fmt (gl,e) =
  let pp_elem fmt e =
    match e with
    | IsInit -> Format.fprintf fmt "init"
    | Expr e -> Printers.pp_expr fmt e
  in 
       Format.fprintf fmt "%a -> %a"
         (fprintf_list ~sep:"; "
            (fun fmt (e,b) -> if b then pp_elem fmt e else Format.fprintf fmt "not(%a)" pp_elem e)) gl
         pp_elem e
  
let concatenate_ge gel1 posneg gel2 =
  List.fold_left (
      fun accu (g2,e2) ->
      List.fold_left (
          fun accu (g1,e1) ->
          ((e1, posneg)::g1@g2, e2)::accu
        ) accu gel1
    ) [] gel2
  
let add_init defs vid =
  Hashtbl.add defs vid [[], IsInit]
  
let rec rewrite defs expr : guarded_expr list =
    match expr.expr_desc with
    | Expr_const _ | Expr_appl _ -> [[], Expr expr]
    | Expr_ident id ->
       if Hashtbl.mem defs id then
         Hashtbl.find defs id
       else
         (* id should be an input *)
         [[], Expr expr]
    | Expr_ite (g, e1, e2) ->
       let g = rewrite defs g and
           e1 = rewrite defs e1 and
           e2 = rewrite defs e2 in
       (concatenate_ge g true e1)@
         (concatenate_ge g false e2)
    | Expr_merge (g, branches) ->
       assert false (* TODO *)
      
    | Expr_when (e, _, _) -> rewrite defs e
    | Expr_arrow _ -> [[], IsInit] (* At this point the only arrow should be true -> false *)
    | Expr_tuple _  | Expr_fby _ 
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
      let select_fun (elem',_) =
        match elem, elem' with
        | IsInit, IsInit -> true
        | Expr e, Expr e' ->
           Corelang.is_eq_expr e e'
        | _ -> false
      in
      let sel, others_guards = List.partition select_fun guards in
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
      | _ -> assert false (* more then one element selected. Should
                             not happen , or trival dead code like if
                             x then if not x then dead code *)
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
       let _ = (
           Format.eprintf "Expr is %a@." Printers.pp_expr elem;
           match elem.expr_desc with
           | Expr_const _ -> Format.eprintf "a const@."
                           
           | Expr_ident _ -> Format.eprintf "an ident@."
           | _ -> Format.eprintf "something else@."
         )
       in
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
  let sorted_eqs = Scheduling.sort_equations_from_schedule nd schedule in
  let defs : (ident,  guarded_expr list) Hashtbl.t = Hashtbl.create 13 in
  let add_def = add_def defs in
  (* Registering node equations *)
  let mem_defs =
    List.fold_left (fun accu eq ->
        match eq.eq_lhs with
        | [vid] ->
           (* Only focus on non memory definitions *)
           if not (List.exists (fun v -> v.var_id = vid) mems) then (
             add_def vid eq.eq_rhs;
             accu
           )
           else
             (
               match eq.eq_rhs.expr_desc with
               | Expr_pre def_m ->
                  (vid, rewrite defs def_m)::accu
               | _ -> assert false
             )
        | _ -> assert false (* should have been removed by normalization *)
      ) [] sorted_eqs
  in
  (* Printing memories definitions *)
  report ~level:3
    (fun fmt ->
      Format.fprintf fmt
        "%a"
        (Utils.fprintf_list ~sep:"@."
           (fun fmt (m,mdefs) ->
             Format.fprintf fmt
               "%s -> @[<v 0>[%a@] ]@."
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
        "Init:@.%a@.Step@.%a"
        (Utils.fprintf_list ~sep:"@."
           (fun fmt (m,mdefs) ->
             Format.fprintf fmt
               "%s -> @[<v 0>[%a@] ]@."
               m
               (Utils.fprintf_list ~sep:"@ "
                  pp_guard_expr) mdefs
        ))
        init_defs
        (Utils.fprintf_list ~sep:"@."
           (fun fmt (m,mdefs) ->
             Format.fprintf fmt
               "%s -> @[<v 0>[%a@] ]@."
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
