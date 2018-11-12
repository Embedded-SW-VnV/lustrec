open Lustre_types
open Utils
open Seal_utils			
			
(******************************************************************************)
(* Computing a slice of a node, selecting only some variables, based on       *)
(* their COI (cone of influence)                                              *)
(******************************************************************************)

(* Basic functions to search into nodes. Could be moved to corelang eventually *)
let is_variable nd vid = 
  List.exists
    (fun v -> v.var_id = vid)
    nd.node_locals
  
let find_variable nd vid = 
  List.find
    (fun v -> v.var_id = vid)
    nd.node_locals

(* Returns the vars required to compute v. 
   Memories are specifically identified. *)
let coi_var deps nd v =
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
         if is_variable nd vname' then
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
  report ~level:3
    (fun fmt -> Format.fprintf fmt "COI of var %s: (%a // %a)@."
		  v.var_id
		  (fprintf_list ~sep:"," Format.pp_print_string) (ISet.elements vset)
		  (fprintf_list ~sep:"," Format.pp_print_string) (ISet.elements memset)
    )  ;
  vset, memset
  
	  
(* Computes the variables required to compute vl. Variables /seen/ do not need
     to be computed *)
let rec coi_vars deps nd vl seen =
  let coi_vars = coi_vars deps nd in
  List.fold_left
    (fun accu v ->
     let vset, memset = coi_var deps nd v in
     (* We handle the new mems discovered in the coi *)
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
           (find_variable nd vid)::accu
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
    
    
(* compute the coi of vars_to_keeps in node nd *)
let compute_sliced_vars vars_to_keep deps nd =
  ISet.elements (coi_vars deps nd vars_to_keep []) 





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
      report ~level:2 (fun fmt -> Format.fprintf fmt "No visible output variable, subtituting with provided vars@ ");
      vars_to_keep
    )
    | l -> l
  in
  let locals =
    List.filter (fun v -> List.mem v.var_id coi_vars) nd.node_locals
  in

  report ~level:3 (fun fmt -> Format.fprintf fmt "Scheduling node@.");
  
  (* Split tuples while sorting eqs *)
  let sorted_eqs = Scheduling.sort_equations_from_schedule nd msch.Scheduling_type.schedule in

  report ~level:3 (fun fmt -> Format.fprintf fmt "Scheduled node@.");

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
