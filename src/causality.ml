(********************************************************************)
(*                                                                  *)
(*  The LustreC compiler toolset   /  The LustreC Development Team  *)
(*  Copyright 2012 -    --   ONERA - CNRS - INPT - LIFL             *)
(*                                                                  *)
(*  LustreC is free software, distributed WITHOUT ANY WARRANTY      *)
(*  under the terms of the GNU Lesser General Public License        *)
(*  version 2.1.                                                    *)
(*                                                                  *) 
(*  This file was originally from the Prelude compiler              *)
(*                                                                  *) 
(********************************************************************)


(** Simple modular syntactic causality analysis. Can reject correct
    programs, especially if the program is not flattened first. *)
open Utils
open Lustre_types
open Corelang
open Graph


type identified_call = eq * tag
type error =
  | DataCycle of ident list list (* multiple failed partitions at once *) 
  | NodeCycle of ident list

exception Error of error


  
(* Dependency of mem variables on mem variables is cut off 
   by duplication of some mem vars into local node vars.
   Thus, cylic dependency errors may only arise between no-mem vars.
   non-mem variables are:
   - constants/inputs: not needed for causality/scheduling, needed only for detecting useless vars
   - read mems (fake vars): same remark as above.
   - outputs: decoupled from mems, if necessary
   - locals
   - instance vars (fake vars): simplify causality analysis
   
   global constants are not part of the dependency graph.
   
   no_mem' = combinational(no_mem, mem);
   => (mem -> no_mem' -> no_mem)

   mem' = pre(no_mem, mem);
   => (mem' -> no_mem), (mem -> mem')
   
   Global roadmap:
   - compute two dep graphs g (non-mem/non-mem&mem) and g' (mem/mem)
   - check cycles in g (a cycle means a dependency error)
   - break cycles in g' (it's legal !):
     - check cycles in g'
     - if any, introduce aux var to break cycle, then start afresh
   - insert g' into g
   - return g
*)

(* Tests whether [v] is a root of graph [g], i.e. a source *)
let is_graph_root v g =
  IdentDepGraph.in_degree g v = 0

(* Computes the set of graph roots, i.e. the sources of acyclic graph [g] *)
let graph_roots g =
  IdentDepGraph.fold_vertex
    (fun v roots -> if is_graph_root v g then v::roots else roots)
    g []

let add_edges src tgt g =
 (*List.iter (fun s -> List.iter (fun t -> Format.eprintf "add %s -> %s@." s t) tgt) src;*)
  List.iter
    (fun s ->
      List.iter
	(fun t -> IdentDepGraph.add_edge g s t)
	tgt)
    src;
  g

let add_vertices vtc g =
 (*List.iter (fun t -> Format.eprintf "add %s@." t) vtc;*)
  List.iter (fun v -> IdentDepGraph.add_vertex g v) vtc;
  g

let new_graph () =
  IdentDepGraph.create ()

(* keep subgraph of [gr] consisting of nodes accessible from node [v] *)
let slice_graph gr v =
  begin
    let gr' = new_graph () in
    IdentDepGraph.add_vertex gr' v;
    Bfs.iter_component (fun v -> IdentDepGraph.iter_succ (fun s -> IdentDepGraph.add_vertex gr' s; IdentDepGraph.add_edge gr' v s) gr v) gr v;
    gr'
  end

    
module ExprDep = struct
  let get_node_eqs nd =
    let eqs, auts = get_node_eqs nd in
    if auts != [] then assert false (* No call on causality on a Lustre model
				       with automaton. They should be expanded by now. *);
    eqs
      
  let instance_var_cpt = ref 0

(* read vars represent input/mem read-only vars,
   they are not part of the program/schedule,
   as they are not assigned,
   but used to compute useless inputs/mems.
   a mem read var represents a mem at the beginning of a cycle  *)
  let mk_read_var id =
    Format.sprintf "#%s" id

(* instance vars represent node instance calls,
   they are not part of the program/schedule,
   but used to simplify causality analysis
*)
  let mk_instance_var id =
    incr instance_var_cpt; Format.sprintf "!%s_%d" id !instance_var_cpt

  let is_read_var v = v.[0] = '#'

  let is_instance_var v = v.[0] = '!'

  let is_ghost_var v = is_instance_var v || is_read_var v

  let undo_read_var id =
    assert (is_read_var id);
    String.sub id 1 (String.length id - 1)

  let undo_instance_var id =
    assert (is_instance_var id);
    String.sub id 1 (String.length id - 1)

  let eq_memory_variables mems eq =
    let rec match_mem lhs rhs mems =
      match rhs.expr_desc with
      | Expr_fby _
      | Expr_pre _    -> List.fold_right ISet.add lhs mems
      | Expr_tuple tl -> 
	 let lhs' = (transpose_list [lhs]) in
	 List.fold_right2 match_mem lhs' tl mems
      | _             -> mems in
    match_mem eq.eq_lhs eq.eq_rhs mems

  let node_memory_variables nd =
    List.fold_left eq_memory_variables ISet.empty (get_node_eqs nd)

  let node_input_variables nd =
    List.fold_left (fun inputs v -> ISet.add v.var_id inputs) ISet.empty 
      (if nd.node_iscontract then
         nd.node_inputs@nd.node_outputs
       else
         nd.node_inputs)
    
  let node_output_variables nd =
    List.fold_left (fun outputs v -> ISet.add v.var_id outputs) ISet.empty
      (if nd.node_iscontract then [] else nd.node_outputs)

  let node_local_variables nd =
    List.fold_left (fun locals v -> ISet.add v.var_id locals) ISet.empty nd.node_locals

  let node_constant_variables nd =
    List.fold_left (fun locals v -> if v.var_dec_const then ISet.add v.var_id locals else locals) ISet.empty nd.node_locals

  let node_auxiliary_variables nd =
    ISet.diff (node_local_variables nd) (node_memory_variables nd)

  let node_variables nd =
    let inputs = node_input_variables nd in
    let inoutputs = List.fold_left (fun inoutputs v -> ISet.add v.var_id inoutputs) inputs nd.node_outputs in
    List.fold_left (fun vars v -> ISet.add v.var_id vars) inoutputs nd.node_locals

(* computes the equivalence relation relating variables 
   in the same equation lhs, under the form of a table 
   of class representatives *)
  let eqs_eq_equiv eqs =
    let eq_equiv = Hashtbl.create 23 in
    List.iter (fun eq ->
      let first = List.hd eq.eq_lhs in
      List.iter (fun v -> Hashtbl.add eq_equiv v first) eq.eq_lhs
    )
      eqs;
    eq_equiv
    
  let node_eq_equiv nd = eqs_eq_equiv  (get_node_eqs nd)
  
(* Create a tuple of right dimension, according to [expr] type, *)
(* filled with variable [v] *)
  let adjust_tuple v expr =
    match expr.expr_type.Types.tdesc with
    | Types.Ttuple tl -> duplicate v (List.length tl)
    | _         -> [v]


  (* Add dependencies from lhs to rhs in [g, g'], *)
  (* no-mem/no-mem and mem/no-mem in g            *)
  (* mem/mem in g'                                *)
  (*     match (lhs_is_mem, ISet.mem x mems) with
	 | (false, true ) -> (add_edges [x] lhs g,
	 g')
	 | (false, false) -> (add_edges lhs [x] g,
	 g')
	 | (true , false) -> (add_edges lhs [x] g,
	 g')
	 | (true , true ) -> (g,
	 add_edges [x] lhs g')
  *)
  let add_eq_dependencies mems inputs node_vars eq (g, g') =
    let add_var lhs_is_mem lhs x (g, g') =
      if is_instance_var x || ISet.mem x node_vars then
	if ISet.mem x mems
	then
	  let g = add_edges lhs [mk_read_var x] g in
	  if lhs_is_mem
	  then
	    (g, add_edges [x] lhs g')
	  else
	    (add_edges [x] lhs g, g')
	else
	  let x = if ISet.mem x inputs then mk_read_var x else x in
	  (add_edges lhs [x] g, g')
      else (add_edges lhs [mk_read_var x] g, g') (* x is a global constant, treated as a read var *)
    in
  (* Add dependencies from [lhs] to rhs clock [ck]. *)
    let rec add_clock lhs_is_mem lhs ck g =
    (*Format.eprintf "add_clock %a@." Clocks.print_ck ck;*)
      match (Clocks.repr ck).Clocks.cdesc with
      | Clocks.Con (ck', cr, _)   -> add_var lhs_is_mem lhs (Clocks.const_of_carrier cr) (add_clock lhs_is_mem lhs ck' g)
      | Clocks.Ccarrying (_, ck') -> add_clock lhs_is_mem lhs ck' g
      | _                         -> g 
    in
    let rec add_dep lhs_is_mem lhs rhs g =
    (* Add mashup dependencies for a user-defined node instance [lhs] = [f]([e]) *)
    (* i.e every input is connected to every output, through a ghost var *)
      let mashup_appl_dependencies f e g =
	let f_var = mk_instance_var (Format.sprintf "%s_%d" f eq.eq_loc.Location.loc_start.Lexing.pos_lnum) in
	List.fold_right (fun rhs -> add_dep lhs_is_mem (adjust_tuple f_var rhs) rhs)
	  (expr_list_of_expr e) (add_var lhs_is_mem lhs f_var g) 
      in
      match rhs.expr_desc with
      | Expr_const _    -> g
      | Expr_fby (e1, e2)  -> add_dep true lhs e2 (add_dep false lhs e1 g)
      | Expr_pre e      -> add_dep true lhs e g
      | Expr_ident x -> add_var lhs_is_mem lhs x (add_clock lhs_is_mem lhs rhs.expr_clock g)
      | Expr_access (e1, d)
      | Expr_power (e1, d) -> add_dep lhs_is_mem lhs e1 (add_dep lhs_is_mem lhs (expr_of_dimension d) g)
      | Expr_array a -> List.fold_right (add_dep lhs_is_mem lhs) a g
      | Expr_tuple t -> List.fold_right2 (fun l r -> add_dep lhs_is_mem [l] r) lhs t g
      | Expr_merge (c, hl) -> add_var lhs_is_mem lhs c (List.fold_right (fun (_, h) -> add_dep lhs_is_mem lhs h) hl g)
      | Expr_ite   (c, t, e) -> add_dep lhs_is_mem lhs c (add_dep lhs_is_mem lhs t (add_dep lhs_is_mem lhs e g))
      | Expr_arrow (e1, e2)  -> add_dep lhs_is_mem lhs e2 (add_dep lhs_is_mem lhs e1 g)
      | Expr_when  (e, c, _)  -> add_dep lhs_is_mem lhs e (add_var lhs_is_mem lhs c g)
      | Expr_appl (f, e, None) ->
	 if Basic_library.is_expr_internal_fun rhs
      (* tuple component-wise dependency for internal operators *)
	 then
	   List.fold_right (add_dep lhs_is_mem lhs) (expr_list_of_expr e) g
      (* mashed up dependency for user-defined operators *)
	 else
	   mashup_appl_dependencies f e g
      | Expr_appl (f, e, Some c) ->
	 mashup_appl_dependencies f e (add_dep lhs_is_mem lhs c g)
    in
    let g =
      List.fold_left
	(fun g lhs ->
	  if ISet.mem lhs mems then
	    add_vertices [lhs; mk_read_var lhs] g
	  else
	    add_vertices [lhs] g
	)
	g eq.eq_lhs
    in
    add_dep false eq.eq_lhs eq.eq_rhs (g, g')
      

  (* Returns the dependence graph for node [n] *)
  let dependence_graph mems inputs node_vars n =
    instance_var_cpt := 0;
    let g = new_graph (), new_graph () in
    (* Basic dependencies *)
    let g = List.fold_right (add_eq_dependencies mems inputs node_vars) (get_node_eqs n) g in
    (* TODO Xavier: un essai ci dessous. Ca n'a pas l'air de résoudre le pb. Il
       faut imposer que les outputs dépendent des asserts pour identifier que les
       fcn calls des asserts sont évalués avant le noeuds *)
    
    (* (\* In order to introduce dependencies between assert expressions and the node, *)
    (*    we build an artificial dependency between node output and each assert *)
    (*    expr. While these are not valid equations, they should properly propage in *)
    (*    function add_eq_dependencies *\) *)
    (* let g = *)
    (*   let output_vars_as_lhs = ISet.elements (node_output_variables n) in *)
    (*   List.fold_left (fun g ae -> *)
    (*     let fake_eq = mkeq Location.dummy_loc (output_vars_as_lhs, ae.assert_expr) in *)
    (*   add_eq_dependencies mems inputs node_vars fake_eq g *)
    (* ) g n.node_asserts in  *)
    g

end

module NodeDep = struct

  module ExprModule =
  struct
    type t = expr
    let compare = compare
    let hash n = Hashtbl.hash n
    let equal n1 n2 = n1 = n2
  end

  module ESet = Set.Make(ExprModule)

  let rec get_expr_calls prednode expr = 
    match expr.expr_desc with
    | Expr_const _ 
    | Expr_ident _ -> ESet.empty
    | Expr_access (e, _)
    | Expr_power (e, _) -> get_expr_calls prednode e
    | Expr_array t
    | Expr_tuple t -> List.fold_right (fun x set -> ESet.union (get_expr_calls prednode x) set) t ESet.empty
    | Expr_merge (_,hl) -> List.fold_right (fun (_,h) set -> ESet.union (get_expr_calls prednode h) set) hl ESet.empty
    | Expr_fby (e1,e2)
    | Expr_arrow (e1,e2) -> ESet.union (get_expr_calls prednode e1) (get_expr_calls prednode e2)
    | Expr_ite   (c, t, e) -> ESet.union (get_expr_calls prednode c) (ESet.union (get_expr_calls prednode t) (get_expr_calls prednode e))
    | Expr_pre e 
    | Expr_when (e,_,_) -> get_expr_calls prednode e
    | Expr_appl (id,e, _) ->
       if not (Basic_library.is_expr_internal_fun expr) && prednode id
       then ESet.add expr (get_expr_calls prednode e)
       else (get_expr_calls prednode e)

  let get_eexpr_calls prednode ee =
    get_expr_calls prednode ee.eexpr_qfexpr
    
  let get_callee expr =
    match expr.expr_desc with
    | Expr_appl (id, args, _) -> Some (id, expr_list_of_expr args)
    | _ -> None

  let accu f init objl = List.fold_left (fun accu o -> ESet.union accu (f o)) init objl 

  let get_eq_calls prednode eq = get_expr_calls prednode eq.eq_rhs
                      
  let rec get_stmt_calls prednode s =
    match s with Eq eq -> get_eq_calls prednode eq | Aut aut -> get_aut_calls prednode aut 
  and get_aut_calls prednode aut =
    let get_handler_calls prednode h =
      let get_cond_calls c = accu (fun (_,e,_,_) -> get_expr_calls prednode e) ESet.empty c in
      let until = get_cond_calls h.hand_until in
      let unless = get_cond_calls h.hand_unless in
      let calls = ESet.union until unless in 
      let calls = accu (get_stmt_calls prednode) calls h.hand_stmts in
      let calls = accu (fun a -> get_expr_calls prednode a.assert_expr) calls h.hand_asserts in
      (* let calls = accu xx calls h.hand_annots in *) (* TODO: search for calls in eexpr *)
      calls
    in
    accu (get_handler_calls prednode) ESet.empty aut.aut_handlers
    
  let get_calls prednode nd =
    let eqs, auts = get_node_eqs nd in
    let deps = accu (get_eq_calls prednode) ESet.empty eqs in
    let deps = accu (get_aut_calls prednode) deps auts in
    ESet.elements deps

  let get_contract_calls prednode c =
    let deps = accu (get_stmt_calls prednode) ESet.empty c.stmts in
    let deps = accu (get_eexpr_calls prednode) deps ( c.assume @ c.guarantees @ (List.fold_left (fun accu m -> accu @ m.require @ m.ensure ) [] c.modes)) in
    let id_deps = List.map (fun e -> fst (desome (get_callee e))) (ESet.elements deps) in  
    let id_deps = (List.fold_left (fun accu imp -> imp.import_nodeid::accu) [] c.imports) @ id_deps in  
    id_deps
    
  let dependence_graph prog =
    let g = new_graph () in
    let g = List.fold_right 
      (fun td accu -> (* for each node we add its dependencies *)
	match td.top_decl_desc with 
	| Node nd ->
	  (*Format.eprintf "Computing deps of node %s@.@?" nd.node_id; *)
	   let accu = add_vertices [nd.node_id] accu in
	   let deps = List.map
	     (fun e -> fst (desome (get_callee e)))
	     (get_calls (fun _ -> true) nd) 
	   in
	     (* Adding assert expressions deps *)
	   let deps_asserts =
	     let prednode = (fun _ -> true) in (* what is this about? *)
	     List.map
	       (fun e -> fst (desome (get_callee e)))
 	       (ESet.elements
		  (List.fold_left
		     (fun accu assert_expr -> ESet.union accu (get_expr_calls prednode assert_expr))
		     ESet.empty
		     (List.map (fun _assert -> _assert.assert_expr) nd.node_asserts)
		  )
	       )
      	   in
           let deps_spec = match nd.node_spec with
             | None -> []
             | Some (NodeSpec id) -> [id]
             | Some (Contract c) -> get_contract_calls (fun _ -> true) c
                                  
           in
	   (*Format.eprintf "%a@.@?" (Utils.fprintf_list ~sep:"@." Format.pp_print_string) deps; *)
	   add_edges [nd.node_id] (deps@deps_asserts@deps_spec) accu
	| _ -> assert false (* should not happen *)
	   
      ) prog g in
    g   
      
  let rec filter_static_inputs inputs args =
    match inputs, args with
    | []   , [] -> []
    | v::vq, a::aq -> if v.var_dec_const && Types.is_dimension_type v.var_type then (dimension_of_expr a) :: filter_static_inputs vq aq else filter_static_inputs vq aq
    | _ -> assert false

  let compute_generic_calls prog =
    List.iter
      (fun td ->
	match td.top_decl_desc with 
	| Node nd ->
	   let prednode n = is_generic_node (node_from_name n) in
	   nd.node_gencalls <- get_calls prednode nd
	| _ -> ()
	   
      ) prog

end


module CycleDetection = struct

  (* ---- Look for cycles in a dependency graph *)
  module Cycles = Graph.Components.Make (IdentDepGraph)

  let mk_copy_var n id =
    let used name =
      (List.exists (fun v -> v.var_id = name) n.node_locals)
      || (List.exists (fun v -> v.var_id = name) n.node_inputs)
      || (List.exists (fun v -> v.var_id = name) n.node_outputs)
    in mk_new_name used id

  let mk_copy_eq n var =
    let var_decl = get_node_var var n in
    let cp_var = mk_copy_var n var in
    let expr =
      { expr_tag = Utils.new_tag ();
	expr_desc = Expr_ident var;
	expr_type = var_decl.var_type;
	expr_clock = var_decl.var_clock;
	expr_delay = Delay.new_var ();
	expr_annot = None;
	expr_loc = var_decl.var_loc } in
    { var_decl with var_id = cp_var; var_orig = false },
    mkeq var_decl.var_loc ([cp_var], expr)

  let wrong_partition g partition =
    match partition with
    | [id]    -> IdentDepGraph.mem_edge g id id
    | _::_::_ -> true
    | []      -> assert false

  (* Checks that the dependency graph [g] does not contain a cycle. Raises
     [Cycle partition] if the succession of dependencies [partition] forms a cycle *)
  let check_cycles g =
    let scc_l = Cycles.scc_list g in
    let algebraic_loops = List.filter (wrong_partition g) scc_l in
    if List.length algebraic_loops > 0 then
      raise (Error (DataCycle algebraic_loops))
	(* We extract a hint to resolve the cycle: for each variable in the cycle
	   which is defined by a call, we return the name of the node call and
	   its specific id *)

  (* Creates the sub-graph of [g] restricted to vertices and edges in partition *)
  let copy_partition g partition =
    let copy_g = IdentDepGraph.create () in
    IdentDepGraph.iter_edges
      (fun src tgt ->
	if List.mem src partition && List.mem tgt partition
	then IdentDepGraph.add_edge copy_g src tgt)
      g

      
  (* Breaks dependency cycles in a graph [g] by inserting aux variables.
     [head] is a head of a non-trivial scc of [g]. 
     In Lustre, this is legal only for mem/mem cycles *)
  let break_cycle head cp_head g =
    let succs = IdentDepGraph.succ g head in
    IdentDepGraph.add_edge g head cp_head;
    IdentDepGraph.add_edge g cp_head (ExprDep.mk_read_var head);
    List.iter
      (fun s ->
	IdentDepGraph.remove_edge g head s;
	IdentDepGraph.add_edge    g s cp_head)
      succs

  (* Breaks cycles of the dependency graph [g] of memory variables [mems]
     belonging in node [node]. Returns:
     - a list of new auxiliary variable declarations
     - a list of new equations
     - a modified acyclic version of [g]
  *)
  let break_cycles node mems g =
    let eqs , auts = get_node_eqs node in
    assert (auts = []); (* TODO: check: For the moment we assume that auts are expanded by now *)
    let (mem_eqs, non_mem_eqs) = List.partition (fun eq -> List.exists (fun v -> ISet.mem v mems) eq.eq_lhs) eqs in
    let rec break vdecls mem_eqs g =
      let scc_l = Cycles.scc_list g in
      let wrong = List.filter (wrong_partition g) scc_l in
      match wrong with
      | []              -> (vdecls, non_mem_eqs@mem_eqs, g)
      | [head]::_       ->
	 begin
	   IdentDepGraph.remove_edge g head head;
	   break vdecls mem_eqs g
	 end
      | (head::part)::_ -> 
	 begin
	   let vdecl_cp_head, cp_eq = mk_copy_eq node head in
	   let pvar v = List.mem v part in
	   let fvar v = if v = head then vdecl_cp_head.var_id else v in
	   let mem_eqs' = List.map (eq_replace_rhs_var pvar fvar) mem_eqs in
	   break_cycle head vdecl_cp_head.var_id g;
	   break (vdecl_cp_head::vdecls) (cp_eq::mem_eqs') g
	 end
      | _               -> assert false
    in break [] mem_eqs g

end

(* Module used to compute static disjunction of variables based upon their clocks. *)
module Disjunction =
struct
  module ClockedIdentModule =
  struct
    type t = var_decl
    let root_branch vdecl = Clocks.root vdecl.var_clock, Clocks.branch vdecl.var_clock
    let compare v1 v2 = compare (root_branch v2, v2.var_id) (root_branch v1, v1.var_id)
  end

  module CISet = Set.Make(ClockedIdentModule)

  (* map: var |-> list of disjoint vars, sorted in increasing branch length order,
     maybe removing shorter branches *)
  type disjoint_map = (ident, CISet.t) Hashtbl.t

  let pp_ciset fmt t =
    begin
      Format.fprintf fmt "{@ ";
      CISet.iter (fun s -> Format.fprintf fmt "%a@ " Printers.pp_var_name s) t;
      Format.fprintf fmt "}@."
    end

  let clock_disjoint_map vdecls =
    let map = Hashtbl.create 23 in
    begin
      List.iter
	(fun v1 -> let disj_v1 =
		     List.fold_left
		       (fun res v2 -> if Clocks.disjoint v1.var_clock v2.var_clock then CISet.add v2 res else res)
		       CISet.empty
		       vdecls in
		   (* disjoint vdecls are stored in increasing branch length order *)
		   Hashtbl.add map v1.var_id disj_v1)
	vdecls;
      (map : disjoint_map)
    end

  (* merge variables [v] and [v'] in disjunction [map]. Then:
     - the mapping v' becomes v' |-> (map v) inter (map v')
     - the mapping v |-> ... then disappears
     - other mappings become x |-> (map x) \ (if v in x then v else v')
  *)
  let merge_in_disjoint_map map v v' =
    begin
      Hashtbl.replace map v'.var_id (CISet.inter (Hashtbl.find map v.var_id) (Hashtbl.find map v'.var_id));
      Hashtbl.remove map v.var_id;
      Hashtbl.iter (fun x map_x -> Hashtbl.replace map x (CISet.remove (if CISet.mem v map_x then v else v') map_x)) map;
    end

  (* replace variable [v] by [v'] in disjunction [map].
     [v'] is a dead variable. Then:
     - the mapping v' becomes v' |-> (map v)
     - the mapping v |-> ... then disappears
     - all mappings become x |-> ((map x) \ { v}) union ({v'} if v in map x)
  *)
  let replace_in_disjoint_map map v v' =
    begin
      Hashtbl.replace map v'.var_id (Hashtbl.find map v.var_id);
      Hashtbl.remove  map v.var_id;
      Hashtbl.iter (fun x mapx -> Hashtbl.replace map x (if CISet.mem v mapx then CISet.add v' (CISet.remove v mapx) else CISet.remove v' mapx)) map;
    end

  (* remove variable [v] in disjunction [map]. Then:
     - the mapping v |-> ... then disappears
     - all mappings become x |-> (map x) \ { v}
  *)
  let remove_in_disjoint_map map v =
    begin
      Hashtbl.remove map v.var_id;
      Hashtbl.iter (fun x mapx -> Hashtbl.replace map x (CISet.remove v mapx)) map;
    end

  let pp_disjoint_map fmt map =
    begin
      Format.fprintf fmt "{ /* disjoint map */@.";
      Hashtbl.iter (fun k v -> Format.fprintf fmt "%s # { %a }@." k (Utils.fprintf_list ~sep:", " Printers.pp_var_name) (CISet.elements v)) map;
      Format.fprintf fmt "}@."
    end
end

  
let pp_dep_graph fmt g =
  begin
    Format.fprintf fmt "{ /* graph */@.";
    IdentDepGraph.iter_edges (fun s t -> Format.fprintf fmt "%s -> %s@." s t) g;
    Format.fprintf fmt "}@."
  end

let pp_error fmt err =
  match err with
  | NodeCycle trace ->
     Format.fprintf fmt "Causality error, cyclic node calls:@   @[<v 0>%a@]@ "
       (fprintf_list ~sep:",@ " Format.pp_print_string) trace
  | DataCycle traces -> (
     Format.fprintf fmt "Causality error, cyclic data dependencies:@   @[<v 0>%a@]@ "
       (fprintf_list ~sep:";@ "
       (fun fmt trace ->
	 Format.fprintf fmt "@[<v 0>{%a}@]"
	   (fprintf_list ~sep:",@ " Format.pp_print_string)
	   trace
       )) traces
  )
     
(* Merges elements of graph [g2] into graph [g1] *)
let merge_with g1 g2 =
  begin
    IdentDepGraph.iter_vertex (fun v -> IdentDepGraph.add_vertex g1 v) g2;
    IdentDepGraph.iter_edges (fun s t -> IdentDepGraph.add_edge g1 s t) g2
  end

let world = "!!_world"

let add_external_dependency outputs mems g =
  begin
    IdentDepGraph.add_vertex g world;
    ISet.iter (fun o -> IdentDepGraph.add_edge g world o) outputs;
    ISet.iter (fun m -> IdentDepGraph.add_edge g world m) mems;
  end

(* Takes a node and return a pair (node', graph) where node' is node
   rebuilt with the equations enriched with new ones introduced to
   "break cycles" *)
let global_dependency node =
  let mems = ExprDep.node_memory_variables node in
  let inputs =
    ISet.union
      (ExprDep.node_input_variables node)
      (ExprDep.node_constant_variables node) in
  let outputs = ExprDep.node_output_variables node in
  let node_vars = ExprDep.node_variables node in
  let (g_non_mems, g_mems) = ExprDep.dependence_graph mems inputs node_vars node in
  (*Format.eprintf "g_non_mems: %a" pp_dep_graph g_non_mems;
    Format.eprintf "g_mems: %a" pp_dep_graph g_mems;*)
  try
    CycleDetection.check_cycles g_non_mems;
    let (vdecls', eqs', g_mems') = CycleDetection.break_cycles node mems g_mems in
    (*Format.eprintf "g_mems': %a" pp_dep_graph g_mems';*)
    begin
      merge_with g_non_mems g_mems';
      add_external_dependency outputs mems g_non_mems;
      { node with node_stmts = List.map (fun eq -> Eq eq) eqs'; node_locals = vdecls'@node.node_locals }, 
      g_non_mems
    end
  with Error (DataCycle _ as exc) -> (
      raise (Error (exc))
  )

(* A module to sort dependencies among local variables when relying on clocked declarations *)
module VarClockDep =
struct
  let rec get_clock_dep ck =
    match ck.Clocks.cdesc with
    | Clocks.Con (ck ,c ,l) -> l::(get_clock_dep ck)
    | Clocks.Clink ck' 
    | Clocks.Ccarrying (_, ck') -> get_clock_dep ck'
    | _ -> []
      
  let sort locals =
    let g = new_graph () in
    let g = List.fold_left (
      fun g var_decl ->
	let deps = get_clock_dep var_decl.var_clock in
	add_edges [var_decl.var_id] deps g
    ) g locals
    in
    let sorted, no_deps =
      TopologicalDepGraph.fold (fun vid (accu, remaining) -> (
	let select v = v.var_id = vid in
	let selected, not_selected = List.partition select remaining in
	selected@accu, not_selected
      )) g ([],locals)
    in
    no_deps @ sorted
    
end
  
(* Local Variables: *)
(* compile-command:"make -C .." *)
(* End: *)
