open Lustre_types
open Utils
   

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
    Format.eprintf "sliced graph for %a: %a@."
      Printers.pp_var v
      Causality.pp_dep_graph sliced_deps;
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
    Format.eprintf "COI of var %s: (%a // %a)@."
      v.var_id
      (fprintf_list ~sep:"," Format.pp_print_string) (ISet.elements vset)
      (fprintf_list ~sep:"," Format.pp_print_string) (ISet.elements memset)
    ;
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
let slice_node vars_to_keep deps nd =
  let coi_vars =
    compute_sliced_vars vars_to_keep deps nd
  in
  Format.eprintf "COI Vars: %a@."
    (Utils.fprintf_list ~sep:"," Format.pp_print_string)
     coi_vars;
  let outputs =
    List.filter
      (
        fun v -> List.mem v.var_id coi_vars 
      ) nd.node_outputs
  in
  let outputs = match outputs with
      [] -> (
      Format.eprintf "No visible output variable, subtituting with provided vars@ ";
      vars_to_keep
    )
    | l -> l
  in
  let locals =
    List.filter (fun v -> List.mem v.var_id coi_vars) nd.node_locals
  in
  let stmts =
    List.filter (
        fun stmt ->
        match stmt with
        | Aut _ -> assert false
        | Eq eq -> (
          match eq.eq_lhs with
            [vid] -> List.mem vid coi_vars
          | _ -> assert false
        (* should not happen after inlining and normalization *)
        )
      ) nd.node_stmts
  in
  { nd
  with
    node_outputs = outputs;
    node_locals = locals;
    node_stmts = stmts 
  }
