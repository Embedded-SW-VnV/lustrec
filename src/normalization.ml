(********************************************************************)
(*                                                                  *)
(*  The LustreC compiler toolset   /  The LustreC Development Team  *)
(*  Copyright 2012 -    --   ONERA - CNRS - INPT                    *)
(*                                                                  *)
(*  LustreC is free software, distributed WITHOUT ANY WARRANTY      *)
(*  under the terms of the GNU Lesser General Public License        *)
(*  version 2.1.                                                    *)
(*                                                                  *)
(********************************************************************)

open Utils
open Lustre_types
open Corelang
open Format

(* To update thank to some command line options *)
let debug = ref false
          
(** Normalisation iters through the AST of expressions and bind fresh definition
    when some criteria are met. This creation of fresh definition is performed by
    the function mk_expr_alias_opt when the alias argument is on.

    Initial expressions, ie expressions attached a variable in an equation
    definition are not aliased. This non-alias feature is propagated in the
    expression AST for array access and power construct, tuple, and some special
    cases of arrows.

    Two global variables may impact the normalization process:
    - unfold_arrow_active
    - force_alias_ite: when set, bind a fresh alias for then and else
      definitions.
*)

type param_t =
  {
    unfold_arrow_active: bool;
    force_alias_ite: bool;
    force_alias_internal_fun: bool;
  }

let params = ref
               {
                 unfold_arrow_active = false;
                 force_alias_ite = false;
                 force_alias_internal_fun =false;
               }

type norm_ctx_t =
  {
    parentid: ident;
    vars: var_decl list;
    is_output: ident -> bool; 
  }

           
let expr_true loc ck =
{ expr_tag = Utils.new_tag ();
  expr_desc = Expr_const (Const_tag tag_true);
  expr_type = Type_predef.type_bool;
  expr_clock = ck;
  expr_delay = Delay.new_var ();
  expr_annot = None;
  expr_loc = loc }

let expr_false loc ck =
{ expr_tag = Utils.new_tag ();
  expr_desc = Expr_const (Const_tag tag_false);
  expr_type = Type_predef.type_bool;
  expr_clock = ck;
  expr_delay = Delay.new_var ();
  expr_annot = None;
  expr_loc = loc }

let expr_once loc ck =
 { expr_tag = Utils.new_tag ();
  expr_desc = Expr_arrow (expr_true loc ck, expr_false loc ck);
  expr_type = Type_predef.type_bool;
  expr_clock = ck;
  expr_delay = Delay.new_var ();
  expr_annot = None;
  expr_loc = loc }

let is_expr_once =
  let dummy_expr_once = expr_once Location.dummy_loc (Clocks.new_var true) in
  fun expr -> Corelang.is_eq_expr expr dummy_expr_once

let unfold_arrow expr =
 match expr.expr_desc with
 | Expr_arrow (e1, e2) ->
    let loc = expr.expr_loc in
    let ck = List.hd (Clocks.clock_list_of_clock expr.expr_clock) in
    { expr with expr_desc = Expr_ite (expr_once loc ck, e1, e2) }
 | _                   -> assert false



(* Get the equation in [defs] with [expr] as rhs, if any *)
let get_expr_alias defs expr =
 try Some (List.find (fun eq -> Clocks.eq_clock expr.expr_clock eq.eq_rhs.expr_clock && is_eq_expr eq.eq_rhs expr) defs)
 with
 | Not_found -> None
  
(* Replace [expr] with (tuple of) [locals] *)
let replace_expr locals expr =
 match locals with
 | []  -> assert false
 | [v] -> { expr with
   expr_tag = Utils.new_tag ();
   expr_desc = Expr_ident v.var_id }
 | _   -> { expr with
   expr_tag = Utils.new_tag ();
   expr_desc = Expr_tuple (List.map expr_of_vdecl locals) }

  
(* IS IT USED ? TODO 
(* Create an alias for [expr], if none exists yet *)
let mk_expr_alias (parentid, vars) (defs, vars) expr =
(*Format.eprintf "mk_expr_alias %a %a %a@." Printers.pp_expr expr Types.print_ty expr.expr_type Clocks.print_ck expr.expr_clock;*)
  match get_expr_alias defs expr with
  | Some eq ->
    let aliases = List.map (fun id -> List.find (fun v -> v.var_id = id) vars) eq.eq_lhs in
    (defs, vars), replace_expr aliases expr
  | None    ->
    let new_aliases =
      List.map2
	(mk_fresh_var (parentid, vars) expr.expr_loc)
	(Types.type_list_of_type expr.expr_type)
	(Clocks.clock_list_of_clock expr.expr_clock) in
    let new_def =
      mkeq expr.expr_loc (List.map (fun v -> v.var_id) new_aliases, expr)
    in
    (* Format.eprintf "Checking def of alias: %a -> %a@." (fprintf_list ~sep:", " (fun fmt v -> Format.pp_print_string fmt v.var_id)) new_aliases Printers.pp_expr expr; *)
    (new_def::defs, new_aliases@vars), replace_expr new_aliases expr
 *)
  
(* Create an alias for [expr], if [expr] is not already an alias (i.e. an ident)
   and [opt] is true

  
 *)
let mk_expr_alias_opt opt norm_ctx (defs, vars) expr =
  if !debug then
    Log.report ~plugin:"normalization" ~level:2
      (fun fmt -> Format.fprintf  fmt "mk_expr_alias_opt %B %a %a %a@." opt Printers.pp_expr expr Types.print_ty expr.expr_type Clocks.print_ck expr.expr_clock);
  match expr.expr_desc with
  | Expr_ident alias ->
    (defs, vars), expr
  | _                ->
    match get_expr_alias defs expr with
    | Some eq ->
       (* Format.eprintf "Found a preexisting definition@."; *)
      let aliases = List.map (fun id -> List.find (fun v -> v.var_id = id) vars) eq.eq_lhs in
      (defs, vars), replace_expr aliases expr
    | None    ->
       (* Format.eprintf "Didnt found a preexisting definition (opt=%b)@." opt;
        * Format.eprintf "existing defs are: @[[%a@]]@."
        *   (fprintf_list ~sep:"@ "(fun fmt eq ->
        *        Format.fprintf fmt "ck:%a isckeq=%b, , iseq=%b, eq=%a"
        *          Clocks.print_ck eq.eq_rhs.expr_clock
        *          (Clocks.eq_clock expr.expr_clock eq.eq_rhs.expr_clock)
        *          (is_eq_expr eq.eq_rhs expr)
        *          Printers.pp_node_eq eq))
        *   defs; *)
      if opt
      then
	let new_aliases =
	  List.map2
	    (mk_fresh_var (norm_ctx.parentid, (norm_ctx.vars@vars)) expr.expr_loc)
	    (Types.type_list_of_type expr.expr_type)
	    (Clocks.clock_list_of_clock expr.expr_clock) in
	let new_def =
	  mkeq expr.expr_loc (List.map (fun v -> v.var_id) new_aliases, expr)
	in
	(* Typing and Registering machine type *) 
	let _ = if Machine_types.is_active then
                  Machine_types.type_def (norm_ctx.parentid, norm_ctx.vars) new_aliases expr
        in
	(new_def::defs, new_aliases@vars), replace_expr new_aliases expr
      else
	(defs, vars), expr

(* Similar fonctions for dimensions *) 
let mk_dim_alias opt norm_ctx (defs, vars) dim =
  match dim.Dimension.dim_desc with
  | Dimension.Dbool _ | Dint _ 
    | Dident _ -> (defs, vars), dim (* Keep the same *)
  | _ when opt -> (* Cast to expression, normalizing *)
     let e = expr_of_dimension dim in
     let defvars, e = mk_expr_alias_opt true norm_ctx (defs, vars) e in
     defvars, dimension_of_expr e

  | _ -> (defs, vars), dim (* Keep the same *)


let unfold_offsets norm_ctx defvars e offsets =
  let add_offset (defvars, e) d =
    (*Format.eprintf "add_offset %a(%a) %a @." Printers.pp_expr e Types.print_ty e.expr_type Dimension.pp_dimension d; *)
    let defvars, d = mk_dim_alias !params.force_alias_internal_fun norm_ctx defvars d in
    let new_e = 
      { e with
        expr_tag = Utils.new_tag ();
        expr_loc = d.Dimension.dim_loc;
        expr_type = Types.array_element_type e.expr_type;
        expr_desc = Expr_access (e, d) }
    in
    defvars, new_e
(*in (Format.eprintf "= %a @." Printers.pp_expr res; res) *)
  in
  List.fold_left add_offset (defvars, e) offsets 

      
(* Create a (normalized) expression from [ref_e],
   replacing description with [norm_d],
   taking propagated [offsets] into account
   in order to change expression type *)
let mk_norm_expr offsets ref_e norm_d =
  (*Format.eprintf "mk_norm_expr %a %a @." Printers.pp_expr ref_e Printers.pp_expr { ref_e with expr_desc = norm_d};*)
  let drop_array_type ty =
    Types.map_tuple_type Types.array_element_type ty in
  { ref_e with
    expr_desc = norm_d;
    expr_type = Utils.repeat (List.length offsets) drop_array_type ref_e.expr_type }
														
(* normalize_<foo> : defs * used vars -> <foo> -> (updated defs * updated vars) * normalized <foo> *)
let rec normalize_list alias norm_ctx offsets norm_element defvars elist =
  List.fold_right
    (fun t (defvars, qlist) ->
      let defvars, norm_t = norm_element alias norm_ctx offsets defvars t in
      (defvars, norm_t :: qlist)
    ) elist (defvars, [])

let rec normalize_expr ?(alias=true) ?(alias_basic=false) norm_ctx offsets defvars expr =
  (* Format.eprintf "normalize %B %a:%a [%a]@." alias Printers.pp_expr expr Types.print_ty expr.expr_type (Utils.fprintf_list ~sep:"," Dimension.pp_dimension) offsets; *)
  match expr.expr_desc with
  | Expr_const _
    | Expr_ident _ ->
     unfold_offsets norm_ctx defvars expr offsets
  | Expr_array elist ->
     let defvars, norm_elist = normalize_list alias norm_ctx offsets (fun _ -> normalize_array_expr ~alias:true) defvars elist in
     let norm_expr = mk_norm_expr offsets expr (Expr_array norm_elist) in
     mk_expr_alias_opt alias norm_ctx defvars norm_expr
  | Expr_power (e1, d) when offsets = [] ->
     let defvars, norm_e1 = normalize_expr norm_ctx offsets defvars e1 in
     let norm_expr = mk_norm_expr offsets expr (Expr_power (norm_e1, d)) in
     mk_expr_alias_opt alias norm_ctx defvars norm_expr
  | Expr_power (e1, d) ->
     normalize_expr ~alias:alias norm_ctx (List.tl offsets) defvars e1
  | Expr_access (e1, d) ->
     normalize_expr ~alias:alias norm_ctx (d::offsets) defvars e1 
    
  | Expr_tuple elist ->
     let defvars, norm_elist =
       normalize_list alias norm_ctx offsets (fun alias -> normalize_expr ~alias:alias ~alias_basic:false) defvars elist in
     defvars, mk_norm_expr offsets expr (Expr_tuple norm_elist)
  | Expr_appl (id, args, None)
      when Basic_library.is_homomorphic_fun id 
	   && Types.is_array_type expr.expr_type ->
     let defvars, norm_args =
       normalize_list
	 alias
	 norm_ctx
	 offsets
	 (fun _ -> normalize_array_expr ~alias:true)
	 defvars
	 (expr_list_of_expr args)
     in
     defvars, mk_norm_expr offsets expr (Expr_appl (id, expr_of_expr_list args.expr_loc norm_args, None))
  | Expr_appl (id, args, None) when Basic_library.is_expr_internal_fun expr
      && not (!params.force_alias_internal_fun || alias_basic) ->
     let defvars, norm_args = normalize_expr ~alias:true norm_ctx offsets defvars args in
     defvars, mk_norm_expr offsets expr (Expr_appl (id, norm_args, None))
  | Expr_appl (id, args, r) ->
     let defvars, r =
       match r with
       | None -> defvars, None
       | Some r ->
	  let defvars, norm_r = normalize_expr ~alias_basic:true norm_ctx [] defvars r in
	  defvars, Some norm_r
     in
     let defvars, norm_args = normalize_expr norm_ctx [] defvars args in
     let norm_expr = mk_norm_expr [] expr (Expr_appl (id, norm_args, r)) in
     if offsets <> []
     then
       let defvars, norm_expr = normalize_expr norm_ctx [] defvars norm_expr in
       normalize_expr ~alias:alias norm_ctx offsets defvars norm_expr
     else
       mk_expr_alias_opt (alias && (!params.force_alias_internal_fun || alias_basic
				    || not (Basic_library.is_expr_internal_fun expr)))
	 norm_ctx defvars norm_expr
  | Expr_arrow (e1,e2) when !params.unfold_arrow_active && not (is_expr_once expr) ->
     (* Here we differ from Colaco paper: arrows are pushed to the top *)
     normalize_expr ~alias:alias norm_ctx offsets defvars (unfold_arrow expr)
  | Expr_arrow (e1,e2) ->
     let defvars, norm_e1 = normalize_expr norm_ctx offsets defvars e1 in
     let defvars, norm_e2 = normalize_expr norm_ctx offsets defvars e2 in
     let norm_expr = mk_norm_expr offsets expr (Expr_arrow (norm_e1, norm_e2)) in
     mk_expr_alias_opt alias norm_ctx defvars norm_expr
  | Expr_pre e ->
     let defvars, norm_e = normalize_expr norm_ctx offsets defvars e in
     let norm_expr = mk_norm_expr offsets expr (Expr_pre norm_e) in
     mk_expr_alias_opt alias norm_ctx defvars norm_expr
  | Expr_fby (e1, e2) ->
     let defvars, norm_e1 = normalize_expr norm_ctx offsets defvars e1 in
     let defvars, norm_e2 = normalize_expr norm_ctx offsets defvars e2 in
     let norm_expr = mk_norm_expr offsets expr (Expr_fby (norm_e1, norm_e2)) in
     mk_expr_alias_opt alias norm_ctx defvars norm_expr
  | Expr_when (e, c, l) ->
     let defvars, norm_e = normalize_expr norm_ctx offsets defvars e in
     defvars, mk_norm_expr offsets expr (Expr_when (norm_e, c, l))
  | Expr_ite (c, t, e) ->
     let defvars, norm_c = normalize_guard norm_ctx defvars c in
     let defvars, norm_t = normalize_cond_expr  norm_ctx offsets defvars t in
     let defvars, norm_e = normalize_cond_expr  norm_ctx offsets defvars e in
     let norm_expr = mk_norm_expr offsets expr (Expr_ite (norm_c, norm_t, norm_e)) in
     mk_expr_alias_opt alias norm_ctx defvars norm_expr
  | Expr_merge (c, hl) ->
     let defvars, norm_hl = normalize_branches norm_ctx offsets defvars hl in
     let norm_expr = mk_norm_expr offsets expr (Expr_merge (c, norm_hl)) in
     mk_expr_alias_opt alias norm_ctx defvars norm_expr

(* Creates a conditional with a merge construct, which is more lazy *)
(*
  let norm_conditional_as_merge alias node norm_expr offsets defvars expr =
  match expr.expr_desc with
  | Expr_ite (c, t, e) ->
  let defvars, norm_t = norm_expr (alias node offsets defvars t in
  | _ -> assert false
*)
and normalize_branches norm_ctx offsets defvars hl =
  List.fold_right
    (fun (t, h) (defvars, norm_q) ->
      let (defvars, norm_h) = normalize_cond_expr norm_ctx offsets defvars h in
      defvars, (t, norm_h) :: norm_q
    )
    hl (defvars, [])

and normalize_array_expr ?(alias=true) norm_ctx offsets defvars expr =
  (*Format.eprintf "normalize_array %B %a [%a]@." alias Printers.pp_expr expr (Utils.fprintf_list ~sep:"," Dimension.pp_dimension) offsets;*)
  match expr.expr_desc with
  | Expr_power (e1, d) when offsets = [] ->
     let defvars, norm_e1 = normalize_expr norm_ctx offsets defvars e1 in
     defvars, mk_norm_expr offsets expr (Expr_power (norm_e1, d))
  | Expr_power (e1, d) ->
     normalize_array_expr ~alias:alias norm_ctx (List.tl offsets) defvars e1
  | Expr_access (e1, d) -> normalize_array_expr ~alias:alias norm_ctx (d::offsets) defvars e1
  | Expr_array elist when offsets = [] ->
     let defvars, norm_elist = normalize_list alias norm_ctx offsets (fun _ -> normalize_array_expr ~alias:true) defvars elist in
     defvars, mk_norm_expr offsets expr (Expr_array norm_elist)
  | Expr_appl (id, args, None) when Basic_library.is_expr_internal_fun expr ->
     let defvars, norm_args = normalize_list alias norm_ctx offsets (fun _ -> normalize_array_expr ~alias:true) defvars (expr_list_of_expr args) in
     defvars, mk_norm_expr offsets expr (Expr_appl (id, expr_of_expr_list args.expr_loc norm_args, None))
  |  _ -> normalize_expr ~alias:alias norm_ctx offsets defvars expr

and normalize_cond_expr ?(alias=true) norm_ctx offsets defvars expr =
  (* Format.eprintf "normalize_cond %B %a [%a]@." alias Printers.pp_expr expr (Utils.fprintf_list ~sep:"," Dimension.pp_dimension) offsets; *)
  match expr.expr_desc with
  | Expr_access (e1, d) ->
     normalize_cond_expr ~alias:alias norm_ctx (d::offsets) defvars e1
  | Expr_ite (c, t, e) ->
     let defvars, norm_c = normalize_guard norm_ctx defvars c in
     let defvars, norm_t = normalize_cond_expr norm_ctx offsets defvars t in
     let defvars, norm_e = normalize_cond_expr norm_ctx offsets defvars e in
     defvars, mk_norm_expr offsets expr (Expr_ite (norm_c, norm_t, norm_e))
  | Expr_merge (c, hl) ->
     let defvars, norm_hl = normalize_branches norm_ctx offsets defvars hl in
     defvars, mk_norm_expr offsets expr (Expr_merge (c, norm_hl))
  | _ when !params.force_alias_ite ->
     (* Forcing alias creation for then/else expressions *)
     let defvars, norm_expr =
       normalize_expr ~alias:alias norm_ctx offsets defvars expr
     in
     mk_expr_alias_opt true norm_ctx defvars norm_expr
  | _ -> (* default case without the force_alias_ite option *)
     normalize_expr ~alias:alias norm_ctx offsets defvars expr
       
and normalize_guard norm_ctx defvars expr =
  let defvars, norm_expr = normalize_expr ~alias_basic:true norm_ctx [] defvars expr in
  mk_expr_alias_opt true norm_ctx defvars norm_expr

(* outputs cannot be memories as well. If so, introduce new local variable.
*)
let decouple_outputs norm_ctx defvars eq =
  let rec fold_lhs defvars lhs tys cks =
    match lhs, tys, cks with
    | [], [], []          -> defvars, []
    | v::qv, t::qt, c::qc -> let (defs_q, vars_q), lhs_q = fold_lhs defvars qv qt qc in
			     if norm_ctx.is_output v
			     then
			       let newvar = mk_fresh_var (norm_ctx.parentid, norm_ctx.vars) eq.eq_loc t c in
			       let neweq  = mkeq eq.eq_loc ([v], expr_of_vdecl newvar) in
			       (neweq :: defs_q, newvar :: vars_q), newvar.var_id :: lhs_q
			     else
			       (defs_q, vars_q), v::lhs_q
    | _                   -> assert false in
  let defvars', lhs' =
    fold_lhs
      defvars
      eq.eq_lhs
      (Types.type_list_of_type eq.eq_rhs.expr_type)
      (Clocks.clock_list_of_clock eq.eq_rhs.expr_clock) in
  defvars', {eq with eq_lhs = lhs' }

let rec normalize_eq norm_ctx defvars eq =
(*Format.eprintf "normalize_eq %a@." Types.print_ty eq.eq_rhs.expr_type;*)
  match eq.eq_rhs.expr_desc with
  | Expr_pre _
  | Expr_fby _  ->
    let (defvars', eq') = decouple_outputs norm_ctx defvars eq in
    let (defs', vars'), norm_rhs = normalize_expr ~alias:false norm_ctx [] defvars' eq'.eq_rhs in
    let norm_eq = { eq' with eq_rhs = norm_rhs } in
    (norm_eq::defs', vars')
  | Expr_array _ ->
    let (defs', vars'), norm_rhs = normalize_array_expr ~alias:false norm_ctx [] defvars eq.eq_rhs in
    let norm_eq = { eq with eq_rhs = norm_rhs } in
    (norm_eq::defs', vars')
  | Expr_appl (id, _, None) when Basic_library.is_homomorphic_fun id && Types.is_array_type eq.eq_rhs.expr_type ->
    let (defs', vars'), norm_rhs = normalize_array_expr ~alias:false norm_ctx [] defvars eq.eq_rhs in
    let norm_eq = { eq with eq_rhs = norm_rhs } in
    (norm_eq::defs', vars')
  | Expr_appl _ ->
    let (defs', vars'), norm_rhs = normalize_expr ~alias:false norm_ctx [] defvars eq.eq_rhs in
    let norm_eq = { eq with eq_rhs = norm_rhs } in
    (norm_eq::defs', vars')
  | _ ->
    let (defs', vars'), norm_rhs = normalize_cond_expr ~alias:false norm_ctx [] defvars eq.eq_rhs in
    let norm_eq = { eq with eq_rhs = norm_rhs } in
    norm_eq::defs', vars'

let normalize_eq_split norm_ctx defvars eq =
  try
    let defs, vars = normalize_eq norm_ctx defvars eq in
    List.fold_right (fun eq (def, vars) -> 
        let eq_defs = Splitting.tuple_split_eq eq in
        if eq_defs = [eq] then
          eq::def, vars 
        else
          List.fold_left (normalize_eq norm_ctx) (def, vars) eq_defs
      ) defs ([], vars)  
    
  with ex -> (
    Format.eprintf "Issue normalizing eq split: %a@." Printers.pp_node_eq eq;
    raise ex
  )

(* Projecting an eexpr to an eexpr associated to a single
   variable. Returns the updated ee, the bounded variable and the
   associated statement *)
let normalize_pred_eexpr decls norm_ctx (def,vars) ee =
  assert (ee.eexpr_quantifiers = []); (* We do not normalize quantifiers yet. This is for very far future. *)
  (* don't do anything is eexpr is just a variable *)
  let skip =
    match ee.eexpr_qfexpr.expr_desc with
    | Expr_ident _ | Expr_const _ -> true
    | _ -> false
  in
  if skip then
    ee, (def, vars)
  else (
    (* New output variable *)
    let output_id = "spec" ^ string_of_int ee.eexpr_tag in
    let output_var = 
      mkvar_decl 
        ee.eexpr_loc 
        (output_id, 
         mktyp ee.eexpr_loc Tydec_bool, (* It is a predicate, hence a bool *)
         mkclock ee.eexpr_loc Ckdec_any, 
         false (* not a constant *),
         None,
         None
        ) 
    in
    let output_expr = expr_of_vdecl output_var in
    (* Rebuilding an eexpr with a silly expression, just a variable *)
    let ee' = { ee with eexpr_qfexpr = output_expr } in

    (* Now processing a fresh equation output_id = eexpr_qfexpr. We
       inline possible calls within, normalize it and type/clock the
       result.  *)
    let eq = mkeq ee.eexpr_loc ([output_id], ee.eexpr_qfexpr) in


    (* (\* Inlining any calls *\)
     * let nodes = get_nodes decls in
     * let calls = ISet.elements (get_expr_calls nodes ee.eexpr_qfexpr) in
     * let vars, eqs =
     *   if calls = [] && not (eq_has_arrows eq) then
     *     vars, [eq]    
     *   else
     *     assert false (\* TODO *\)
     * in *)
    
    (* Normalizing expr and eqs *)
    let defs, vars = List.fold_left (normalize_eq_split norm_ctx) (def, vars) [eq] in
    let vars = output_var :: vars in 
(*    let todefine =
      List.fold_left
        (fun m x-> if List.exists (fun y-> x.var_id = y.var_id) (locals) then m else ISet.add x.var_id m)
        (ISet.add output_id ISet.empty) vars in
 *)      

    (* Typing / Clocking *)
    try
      ignore (Typing.type_var_decl_list vars !Global.type_env vars);
        (*
    let env = Typing.type_var_decl [] !Global.type_env xxxx output_var in (* typing the variable *)
    (* Format.eprintf "typing var %s: %a@." output_id Types.print_ty output_var.var_type; *)
    let env = Typing.type_var_decl_list (vars@node.node_outputs@node.node_inputs) env (vars@node.node_outputs@node.node_inputs) in
    (*Format.eprintf "Env: %a@.@?" (Env.pp_env Types.print_ty) env;*)
    let undefined_vars = List.fold_left (Typing.type_eq (env, quant_vars@vars) false) todefine defs in
  (* check that table is empty *)
    if (not (ISet.is_empty undefined_vars)) then
      raise (Types.Error (ee.eexpr_loc, Types.Undefined_var undefined_vars));
    
    (*Format.eprintf "normalized eqs %a@.@?" 
      (Utils.fprintf_list ~sep:", " Printers.pp_node_eq) defs;  *)
         *)

    ee', (defs, vars)
    
  with (Types.Error (loc,err)) as exc ->
    eprintf "Typing error for eexpr %a: %a%a%a@."
      Printers.pp_eexpr ee
      Types.pp_error err
      (Utils.fprintf_list ~sep:", " Printers.pp_node_eq) defs
      Location.pp_loc loc
  
      
    ;
    raise exc
                                     
  )
    
   (*
  
  let quant_vars = List.flatten (List.map snd ee.eexpr_quantifiers) in
  (* Calls are first inlined *)
  
  (*Format.eprintf "eexpr %a@.calls: %a@.@?" Printers.pp_eexpr ee (Utils.fprintf_list ~sep:", " (fun fmt nd -> pp_print_string fmt nd.node_id)) calls;  *)
  let (new_locals, eqs) =
    if calls = [] && not (eq_has_arrows eq) then
      (locals, [eq])     
    else ( (* TODO remettre le code. Je l'ai enleve pour des dependances cycliques *)
(*      let new_locals, eqs, asserts = Inliner.inline_eq ~arrows:true eq locals calls in
      (*Format.eprintf "eqs %a@.@?" 
	(Utils.fprintf_list ~sep:", " Printers.pp_node_eq) eqs;  *)
      (new_locals, eqs)
*)
           (locals, [eq])     
 
    ) in
  (* Normalizing expr and eqs *)
    let defs, vars = List.fold_left (normalize_eq_split node) ([], new_locals) eqs in
    let todefine = List.fold_left
    (fun m x-> if List.exists (fun y-> x.var_id = y.var_id) (locals) then m else ISet.add x.var_id m)
    (ISet.add output_id ISet.empty) vars in
  
  try
    let env = Typing.type_var_decl_list quant_vars !Global.type_env quant_vars in
    let env = Typing.type_var_decl [] env output_var in (* typing the variable *)
    (* Format.eprintf "typing var %s: %a@." output_id Types.print_ty output_var.var_type; *)
    let env = Typing.type_var_decl_list (vars@node.node_outputs@node.node_inputs) env (vars@node.node_outputs@node.node_inputs) in
    (*Format.eprintf "Env: %a@.@?" (Env.pp_env Types.print_ty) env;*)
    let undefined_vars = List.fold_left (Typing.type_eq (env, quant_vars@vars) false) todefine defs in
  (* check that table is empty *)
    if (not (ISet.is_empty undefined_vars)) then
      raise (Types.Error (ee.eexpr_loc, Types.Undefined_var undefined_vars));
    
    (*Format.eprintf "normalized eqs %a@.@?" 
      (Utils.fprintf_list ~sep:", " Printers.pp_node_eq) defs;  *)
    ee.eexpr_normalized <- Some (output_var, defs, vars)
    
  with (Types.Error (loc,err)) as exc ->
    eprintf "Typing error for eexpr %a: %a%a%a@."
      Printers.pp_eexpr ee
      Types.pp_error err
      (Utils.fprintf_list ~sep:", " Printers.pp_node_eq) defs
      Location.pp_loc loc
  
      
    ;
    raise exc
                                                 *)    
 

(* We use node local vars to make sure we are creating fresh variables *) 
let normalize_spec decls parentid (in_vars, out_vars, l_vars) s =  
  (* Original set of variables actually visible from here: in/out and
     spec locals (no node locals) *)
  let orig_vars = in_vars @ out_vars @ s.locals in
  (* Format.eprintf "NormSpec: init locals: %a@." Printers.pp_vars s.locals; *)
  let not_is_orig_var v =
    List.for_all ((!=) v) orig_vars in
  let norm_ctx = {
      parentid = parentid;
      vars = in_vars @ out_vars @ l_vars;
      is_output = (fun _ -> false) (* no need to introduce fresh variables for outputs *);
    }
  in
  (* Normalizing existing stmts *)
  let eqs, auts = List.fold_right (fun s (el,al)  -> match s with Eq e -> e::el, al | Aut a -> el, a::al) s.stmts ([], []) in
  if auts != [] then assert false; (* Automata should be expanded by now. *)
  let defsvars = 
    List.fold_left (normalize_eq norm_ctx) ([], orig_vars) eqs
  in
  (* Iterate through predicates and normalize them on the go, creating
     fresh variables for any guarantees/assumes/require/ensure *)
  let process_predicates l defvars =
    (* Format.eprintf "ProcPred: vars: %a@." Printers.pp_vars (snd defvars); *)
    let res = List.fold_right (fun ee (accu, defvars) ->
        let ee', defvars = normalize_pred_eexpr decls norm_ctx defvars ee in
        ee'::accu, defvars
      ) l ([], defvars)
    in
    (* Format.eprintf "ProcStmt: %a@." Printers.pp_node_eqs (fst (snd res));
     * Format.eprintf "ProcPred: vars: %a@." Printers.pp_vars (snd (snd res)); *)
    res
  in

  
  let assume', defsvars = process_predicates s.assume defsvars in
  let guarantees', defsvars = process_predicates s.guarantees defsvars in
  let modes', (defs, vars) =
    List.fold_right (
        fun m (accu_m, defsvars) ->
        let require', defsvars = process_predicates m.require defsvars in
        let ensure', defsvars = process_predicates m.ensure defsvars in
        { m with require = require'; ensure = ensure' }:: accu_m, defsvars
      ) s.modes ([], defsvars)
  in
  
  let new_locals = List.filter not_is_orig_var vars in (* removing inouts and initial locals ones *)
  new_locals, defs,      
  {s with
    (* locals = s.locals @ new_locals; *)
    stmts = [];
    assume = assume';
    guarantees = guarantees';
    modes = modes'
  }
(* let nee _ = () in
 *   (\*normalize_eexpr decls iovars in *\)
 *   List.iter nee s.assume;
 *   List.iter nee s.guarantees;
 *   List.iter (fun m -> 
 *       List.iter nee m.require;
 *     List.iter nee m.ensure
 *     ) s.modes; *)
   

                                                                     
  
  
    
(* The normalization phase introduces new local variables
   - output cannot be memories. If this happen, new local variables acting as
   memories are introduced. 
   - array constants, pre, arrow, fby, ite, merge, calls to node with index
   access
   Thoses values are shared, ie. no duplicate expressions are introduced.

   Concerning specification, a similar process is applied, replacing an
   expression by a list of local variables and definitions
*)

(** normalize_node node returns a normalized node, 
    ie. 
    - updated locals
    - new equations
    -
*)
let normalize_node decls node =
  reset_cpt_fresh ();
  let orig_vars = node.node_inputs@node.node_outputs@node.node_locals in
  let not_is_orig_var v =
    List.for_all ((!=) v) orig_vars in
  let norm_ctx = {
      parentid = node.node_id;
      vars = get_node_vars node;
      is_output = (fun vid -> List.exists (fun v -> v.var_id = vid) node.node_outputs);
    }
  in

  let eqs, auts = get_node_eqs node in
  if auts != [] then assert false; (* Automata should be expanded by now. *)
  let spec, new_vars, eqs =
    begin
      (* Update mutable fields of eexpr to perform normalization of
	 specification.

	 Careful: we do not normalize annotations, since they can have the form
	 x = (a, b, c) *)
      match node.node_spec with
      | None 
        | Some (NodeSpec _) -> node.node_spec, [], eqs
      | Some (Contract s) ->
         let new_locals, new_stmts, s' = normalize_spec
                    decls
                    node.node_id
                    (node.node_inputs, node.node_outputs, node.node_locals)
                    s
         in
         (* Format.eprintf "Normalization bounded new locals: %a@." Printers.pp_vars new_locals;
          * Format.eprintf "Normalization bounded stmts: %a@." Printers.pp_node_eqs new_stmts; *)
         Some (Contract s'), new_locals, new_stmts@eqs
    end
  in
  let defs, vars =
    List.fold_left (normalize_eq norm_ctx) ([], new_vars@orig_vars) eqs in
  (* Normalize the asserts *)
  let vars, assert_defs, asserts =
    List.fold_left (
        fun (vars, def_accu, assert_accu) assert_ ->
	let assert_expr = assert_.assert_expr in
	let (defs, vars'), expr = 
	  normalize_expr 
	    ~alias:true (* forcing introduction of new equations for fcn calls *) 
	    norm_ctx 
	    [] (* empty offset for arrays *)
	    ([], vars) (* defvar only contains vars *)
	    assert_expr
	in
        (*Format.eprintf "New assert vars: %a@.@?" (fprintf_list ~sep:", " Printers.pp_var) vars';*)
	vars', defs@def_accu, {assert_ with assert_expr = expr}::assert_accu
      ) (vars, [], []) node.node_asserts in
  let new_locals = List.filter not_is_orig_var vars in (* we filter out inout
							  vars and initial locals ones *)
  
  let all_locals = node.node_locals @ new_locals in (* we add again, at the
						       beginning of the list the
						       local declared ones *)
  (*Format.eprintf "New locals: %a@.@?" (fprintf_list ~sep:", " Printers.pp_var) new_locals;*)


  (* Updating annotations: traceability and machine types for fresh variables *)
  
  (* Compute traceability info:
     - gather newly bound variables
     - compute the associated expression without aliases
   *)
  let new_annots =
    if !Options.traces then
      begin
	let diff_vars = List.filter (fun v -> not (List.mem v node.node_locals) ) all_locals in
	let norm_traceability = {
	    annots = List.map (fun v ->
	                 let eq =
	                   try
		             List.find (fun eq -> List.exists (fun v' -> v' = v.var_id ) eq.eq_lhs) (defs@assert_defs) 
	                   with Not_found -> 
		             (
		               Format.eprintf "Traceability annotation generation: var %s not found@." v.var_id; 
		               assert false
		             ) 
	                 in
	                 let expr = substitute_expr diff_vars (defs@assert_defs) eq.eq_rhs in
	                 let pair = mkeexpr expr.expr_loc (mkexpr expr.expr_loc (Expr_tuple [expr_of_ident v.var_id expr.expr_loc; expr])) in
	                 Annotations.add_expr_ann node.node_id pair.eexpr_tag ["traceability"];
	                 (["traceability"], pair)
	               ) diff_vars;
	    annot_loc = Location.dummy_loc
	  }
	in
	norm_traceability::node.node_annot
      end
    else
      node.node_annot
  in

  let new_annots =
    List.fold_left (fun annots v ->
        if Machine_types.is_active && Machine_types.is_exportable v then
	  let typ = Machine_types.get_specified_type v in
  	  let typ_name = Machine_types.type_name typ in

	  let loc = v.var_loc in
	  let typ_as_string =
	    mkexpr
	      loc
	      (Expr_const
	         (Const_string typ_name))
	  in
	  let pair = expr_to_eexpr (expr_of_expr_list loc [expr_of_vdecl v; typ_as_string]) in
	  Annotations.add_expr_ann node.node_id pair.eexpr_tag Machine_types.keyword;
	  {annots = [Machine_types.keyword, pair]; annot_loc = loc}::annots
        else
	  annots
      ) new_annots new_locals
  in
  
  
  let node =
    { node with
      node_locals = all_locals;
      node_stmts = List.map (fun eq -> Eq eq) (defs @ assert_defs);
      node_asserts = asserts;
      node_annot = new_annots;
      node_spec = spec;
    }
  in ((*Printers.pp_node Format.err_formatter node;*)
      node
    )

let normalize_inode decls nd =
  reset_cpt_fresh ();
  match nd.nodei_spec with
    None | Some (NodeSpec _) -> nd
    | Some (Contract _) -> assert false
                         
let normalize_decl (decls: program_t) (decl: top_decl) : top_decl =
  match decl.top_decl_desc with
  | Node nd ->
     let decl' = {decl with top_decl_desc = Node (normalize_node decls nd)} in
     update_node nd.node_id decl';
     decl'
  | ImportedNode nd ->
     let decl' = {decl with top_decl_desc = ImportedNode (normalize_inode decls nd)} in
     update_node nd.nodei_id decl';
     decl'
     
    | Include _| Open _ | Const _ | TypeDef _ -> decl

let normalize_prog p decls =
  (* Backend specific configurations for normalization *)
  params := p;

  (* Main algorithm: iterates over nodes *)
  List.map (normalize_decl decls) decls


(* Fake interface for outside uses *)
let mk_expr_alias_opt opt (parentid, ctx_vars) (defs, vars) expr =
  mk_expr_alias_opt
    opt
    {parentid = parentid; vars = ctx_vars; is_output = (fun _ -> false) }
    (defs, vars)
    expr

    
           (* Local Variables: *)
           (* compile-command:"make -C .." *)
           (* End: *)
    
