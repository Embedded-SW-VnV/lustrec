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

(** Main typing module. Classic inference algorithm with destructive
    unification. *)

let debug fmt args = () (* Format.eprintf "%a"  *)
(* Though it shares similarities with the clock calculus module, no code
    is shared.  Simple environments, very limited identifier scoping, no
    identifier redefinition allowed. *)

open Utils
(* Yes, opening both modules is dirty as some type names will be
   overwritten, yet this makes notations far lighter.*)
open Lustre_types
open Corelang
open Format


(* TODO general remark: except in the add_vdecl, it seems to me that
   all the pairs (env, vd_env) should be replace with just env, since
   vd_env is never used and the env element is always extract with a
   fst *)

   
module type EXPR_TYPE_HUB =
sig
  type type_expr 
  val import: Types.Main.type_expr -> type_expr
  val export: type_expr -> Types.Main.type_expr 
end

module Make (T: Types.S) (Expr_type_hub: EXPR_TYPE_HUB with type type_expr = T.type_expr) =  
  struct

    module TP = Type_predef.Make (T)
    include TP
    
    let pp_typing_env fmt env =
      Env.pp_env print_ty fmt env

    (****************************************************************)
    (* Generic functions: occurs, instantiate and generalize         *)
    (****************************************************************)
      
    (** [occurs tvar ty] returns true if the type variable [tvar]
       occurs in type [ty]. False otherwise. *)
    let rec occurs tvar ty =
      let ty = repr ty in
      match type_desc ty with
      | Tvar -> ty=tvar
      | Tarrow (t1, t2) ->
         (occurs tvar t1) || (occurs tvar t2)
      | Ttuple tl ->
         List.exists (occurs tvar) tl
      | Tstruct fl ->
         List.exists (fun (f, t) -> occurs tvar t) fl
      | Tarray (_, t)
        | Tstatic (_, t)
        | Tclock t
        | Tlink t -> occurs tvar t
      | Tenum _ | Tconst _ | Tunivar | Tbasic _ -> false

    (** Promote monomorphic type variables to polymorphic type
       variables. *)
    (* Generalize by side-effects *)
    let rec generalize ty =
      match type_desc ty with
      | Tvar ->
         (* No scopes, always generalize *)
         ty.tdesc <- Tunivar
      | Tarrow (t1,t2) ->
         generalize t1; generalize t2
      | Ttuple tl ->
         List.iter generalize tl
      | Tstruct fl ->
         List.iter (fun (f, t) -> generalize t) fl
      | Tstatic (d, t)
        | Tarray (d, t) -> Dimension.generalize d; generalize t
      | Tclock t
        | Tlink t ->
         generalize t
      | Tenum _ | Tconst _ | Tunivar | Tbasic _ -> ()

    (** Downgrade polymorphic type variables to monomorphic type
       variables *)
    let rec instantiate inst_vars inst_dim_vars ty =
      let ty = repr ty in
      match ty.tdesc with
      | Tenum _ | Tconst _ | Tvar | Tbasic _  -> ty
      | Tarrow (t1,t2) ->
         {ty with tdesc =
                    Tarrow ((instantiate inst_vars inst_dim_vars t1), (instantiate inst_vars inst_dim_vars t2))}
      | Ttuple tlist ->
         {ty with tdesc = Ttuple (List.map (instantiate inst_vars inst_dim_vars) tlist)}
      | Tstruct flist ->
         {ty with tdesc = Tstruct (List.map (fun (f, t) -> (f, instantiate inst_vars inst_dim_vars t)) flist)}
      | Tclock t ->
	 {ty with tdesc = Tclock (instantiate inst_vars inst_dim_vars t)}
      | Tstatic (d, t) ->
	 {ty with tdesc = Tstatic (Dimension.instantiate inst_dim_vars d, instantiate inst_vars inst_dim_vars t)}
      | Tarray (d, t) ->
	 {ty with tdesc = Tarray (Dimension.instantiate inst_dim_vars d, instantiate inst_vars inst_dim_vars t)}
      | Tlink t ->
	 (* should not happen *)
	 {ty with tdesc = Tlink (instantiate inst_vars inst_dim_vars t)}
      | Tunivar ->
         try
           List.assoc ty.tid !inst_vars
         with Not_found ->
           let var = new_var () in
	   inst_vars := (ty.tid, var)::!inst_vars;
	   var



    let basic_coretype_type t =
      if is_real_type t then Tydec_real else
        if is_int_type t then Tydec_int else
          if is_bool_type t then Tydec_bool else
	    assert false

    (* [type_coretype cty] types the type declaration [cty] *)
    let rec type_coretype type_dim cty =
      match (*get_repr_type*) cty with
      | Tydec_any -> new_var ()
      | Tydec_int -> type_int
      | Tydec_real -> (* Type_predef. *)type_real
      (* | Tydec_float -> Type_predef.type_real *)
      | Tydec_bool -> (* Type_predef. *)type_bool
      | Tydec_clock ty -> (* Type_predef. *)type_clock (type_coretype type_dim ty)
      | Tydec_const c -> (* Type_predef. *)type_const c
      | Tydec_enum tl -> (* Type_predef. *)type_enum tl
      | Tydec_struct fl -> (* Type_predef. *)type_struct (List.map (fun (f, ty) -> (f, type_coretype type_dim ty)) fl)
      | Tydec_array (d, ty) ->
         begin
           let d = Dimension.copy (ref []) d in
           type_dim d;
           (* Type_predef. *)type_array d (type_coretype type_dim ty)
         end

    (* [coretype_type] is the reciprocal of [type_typecore] *)
    let rec coretype_type ty =
      match (repr ty).tdesc with
      | Tvar           -> Tydec_any
      | Tbasic _       -> basic_coretype_type ty
      | Tconst c       -> Tydec_const c
      | Tclock t       -> Tydec_clock (coretype_type t)
      | Tenum tl       -> Tydec_enum tl
      | Tstruct fl     -> Tydec_struct (List.map (fun (f, t) -> (f, coretype_type t)) fl)
      | Tarray (d, t)  -> Tydec_array (d, coretype_type t)
      | Tstatic (_, t) -> coretype_type t
      | _         -> assert false

    let get_coretype_definition tname =
      try
        let top = Hashtbl.find type_table (Tydec_const tname) in
        match top.top_decl_desc with
        | TypeDef tdef -> tdef.tydef_desc
        | _ -> assert false
      with Not_found -> raise (Error (Location.dummy_loc, Unbound_type tname))

    let get_type_definition tname =
      type_coretype (fun d -> ()) (get_coretype_definition tname)

    (* Equality on ground types only *)
    (* Should be used between local variables which must have a ground type *)
    let rec eq_ground t1 t2 =
      let t1 = repr t1 in
      let t2 = repr t2 in
      t1==t2 ||
        match t1.tdesc, t2.tdesc with
        | Tbasic t1, Tbasic t2 when t1 == t2 -> true
        | Tenum tl, Tenum tl' when tl == tl' -> true
        | Ttuple tl, Ttuple tl' when List.length tl = List.length tl' -> List.for_all2 eq_ground tl tl'
        | Tstruct fl, Tstruct fl' when List.map fst fl = List.map fst fl' -> List.for_all2 (fun (_, t) (_, t') -> eq_ground t t') fl fl'
        | (Tconst t, _) ->
           let def_t = get_type_definition t in
           eq_ground def_t t2
        | (_, Tconst t)  ->
           let def_t = get_type_definition t in
           eq_ground t1 def_t
        | Tarrow (t1,t2), Tarrow (t1',t2') -> eq_ground t1 t1' && eq_ground t2 t2'
        | Tclock t1', Tclock t2' -> eq_ground t1' t2'
        | Tstatic (e1, t1'), Tstatic (e2, t2')
          | Tarray (e1, t1'), Tarray (e2, t2') -> Dimension.is_eq_dimension e1 e2 && eq_ground t1' t2'
        | _ -> false

    (** [unify t1 t2] unifies types [t1] and [t2]
    using standard destructive unification.
    Raises [Unify (t1,t2)] if the types are not unifiable.
    [t1] is a expected/formal/spec type, [t2] is a computed/real/implem type,
    so in case of unification error: expected type [t1], got type [t2].
    If [sub]-typing is allowed, [t2] may be a subtype of [t1].
    If [semi] unification is required,
    [t1] should furthermore be an instance of [t2]
    and constants are handled differently.*)
    let unify ?(sub=false) ?(semi=false) t1 t2 =
      let rec unif t1 t2 =
        let t1 = repr t1 in
        let t2 = repr t2 in
        if t1==t2 then
          ()
        else
          match t1.tdesc,t2.tdesc with
          (* strictly subtyping cases first *)
          | _ , Tclock t2 when sub && (get_clock_base_type t1 = None) ->
	     unif t1 t2
          | _ , Tstatic (d2, t2) when sub && (get_static_value t1 = None) ->
	     unif t1 t2
          (* This case is not mandatory but will keep "older" types *)
          | Tvar, Tvar ->
             if t1.tid < t2.tid then
               t2.tdesc <- Tlink t1
             else
               t1.tdesc <- Tlink t2
          | Tvar, _ when (not semi) && (not (occurs t1 t2)) ->
             t1.tdesc <- Tlink t2
          | _, Tvar when (not (occurs t2 t1)) ->
             t2.tdesc <- Tlink t1
          | Tarrow (t1,t2), Tarrow (t1',t2') ->
	     begin
               unif t2 t2';
	       unif t1' t1
	     end
          | Ttuple tl, Ttuple tl' when List.length tl = List.length tl' ->
	     List.iter2 unif tl tl'
          | Ttuple [t1]        , _                  -> unif t1 t2
          | _                  , Ttuple [t2]        -> unif t1 t2
          | Tstruct fl, Tstruct fl' when List.map fst fl = List.map fst fl' ->
	     List.iter2 (fun (_, t) (_, t') -> unif t t') fl fl'
          | Tclock _, Tstatic _
            | Tstatic _, Tclock _ -> raise (Unify (t1, t2))
          | Tclock t1', Tclock t2' -> unif t1' t2'
          | Tbasic t1, Tbasic t2 when t1 == t2 -> ()
          | Tunivar, _ | _, Tunivar -> ()
          | (Tconst t, _) ->
	     let def_t = get_type_definition t in
	     unif def_t t2
          | (_, Tconst t)  ->
	     let def_t = get_type_definition t in
	     unif t1 def_t
          | Tenum tl, Tenum tl' when tl == tl' -> ()
          | Tstatic (e1, t1'), Tstatic (e2, t2')
            | Tarray (e1, t1'), Tarray (e2, t2') ->
	     let eval_const =
	       if semi
	       then (fun c -> Some (Dimension.mkdim_ident Location.dummy_loc c))
	       else (fun c -> None) in
	     begin
	       unif t1' t2';
	       Dimension.eval Basic_library.eval_dim_env eval_const e1;
	       Dimension.eval Basic_library.eval_dim_env eval_const e2;
	       Dimension.unify ~semi:semi e1 e2;
	     end
          (* Special cases for machine_types. Rules to unify static types infered
      	 for numerical constants with non static ones for variables with
      	 possible machine types *)
          | Tbasic bt1, Tbasic bt2 when BasicT.is_unifiable bt1 bt2 -> BasicT.unify bt1 bt2
          | _,_ -> raise (Unify (t1, t2))
      in unif t1 t2

    (* Expected type ty1, got type ty2 *)
    let try_unify ?(sub=false) ?(semi=false) ty1 ty2 loc =
      try
        unify ~sub:sub ~semi:semi ty1 ty2
      with
      | Unify _ ->
         raise (Error (loc, Type_clash (ty1,ty2)))
      | Dimension.Unify _ ->
         raise (Error (loc, Type_clash (ty1,ty2)))


    (************************************************)
    (* Typing function for each basic AST construct *)
    (************************************************)

    let rec type_struct_const_field ?(is_annot=false) loc (label, c) =
      if Hashtbl.mem field_table label
      then let tydef = Hashtbl.find field_table label in
           let tydec = (typedef_of_top tydef).tydef_desc in 
           let tydec_struct = get_struct_type_fields tydec in
           let ty_label = type_coretype (fun d -> ()) (List.assoc label tydec_struct) in
           begin
	     try_unify ty_label (type_const ~is_annot loc c) loc;
	     type_coretype (fun d -> ()) tydec
           end
      else raise (Error (loc, Unbound_value ("struct field " ^ label)))

    and type_const ?(is_annot=false) loc c = 
      match c with
      | Const_int _     -> (* Type_predef. *)type_int
      | Const_real _    -> (* Type_predef. *)type_real
      | Const_array ca  -> let d = Dimension.mkdim_int loc (List.length ca) in
		           let ty = new_var () in
		           List.iter (fun e -> try_unify ty (type_const ~is_annot loc e) loc) ca;
		           (* Type_predef. *)type_array d ty
      | Const_tag t     ->
         if Hashtbl.mem tag_table t
         then 
           let tydef = typedef_of_top (Hashtbl.find tag_table t) in
           let tydec =
	     if is_user_type tydef.tydef_desc
	     then Tydec_const tydef.tydef_id
	     else tydef.tydef_desc in
           type_coretype (fun d -> ()) tydec
         else raise (Error (loc, Unbound_value ("enum tag " ^ t)))
      | Const_struct fl ->
         let ty_struct = new_var () in
         begin
           let used =
	     List.fold_left
	       (fun acc (l, c) ->
	         if List.mem l acc
	         then raise (Error (loc, Already_bound ("struct field " ^ l)))
	         else try_unify ty_struct (type_struct_const_field ~is_annot loc (l, c)) loc; l::acc)
	       [] fl in
           try
	     let total = List.map fst (get_struct_type_fields (coretype_type ty_struct)) in
             (*	List.iter (fun l -> Format.eprintf "total: %s@." l) total;
	List.iter (fun l -> Format.eprintf "used: %s@." l) used; *)
	     let undef = List.find (fun l -> not (List.mem l used)) total
	     in raise (Error (loc, Unbound_value ("struct field " ^ undef)))
           with Not_found -> 
	     ty_struct
         end
      | Const_string s | Const_modeid s     -> 
         if is_annot then (* Type_predef. *)type_string else (Format.eprintf "Typing string %s outisde of annot scope@.@?" s; assert false (* string datatype should only appear in annotations *))

    (* The following typing functions take as parameter an environment [env]
   and whether the element being typed is expected to be constant [const]. 
   [env] is a pair composed of:
  - a map from ident to type, associating to each ident, i.e. 
    variables, constants and (imported) nodes, its type including whether
    it is constant or not. This latter information helps in checking constant 
    propagation policy in Lustre.
  - a vdecl list, in order to modify types of declared variables that are
    later discovered to be clocks during the typing process.
     *)
    let check_constant loc const_expected const_real =
      if const_expected && not const_real
      then raise (Error (loc, Not_a_constant))

    let rec type_add_const env const arg targ =
      (*Format.eprintf "Typing.type_add_const %a %a@." Printers.pp_expr arg Types.print_ty targ;*)
      if const
      then let d =
	     if is_dimension_type targ
	     then dimension_of_expr arg
	     else Dimension.mkdim_var () in
           let eval_const id = (* Types. *)get_static_value (Env.lookup_value (fst env) id) in
           Dimension.eval Basic_library.eval_dim_env eval_const d;
           let real_static_type = (* Type_predef. *)type_static d ((* Types. *)dynamic_type targ) in
           (match (* Types. *)get_static_value targ with
            | None    -> ()
            | Some d' -> try_unify targ real_static_type arg.expr_loc);
           real_static_type
      else targ

    (* emulates a subtyping relation between types t and (d : t),
   used during node applications and assignments *)
    and type_subtyping_arg env in_main ?(sub=true) const real_arg formal_type =
      let loc = real_arg.expr_loc in
      let const = const || ((* Types. *)get_static_value formal_type <> None) in
      let real_type = type_add_const env const real_arg (type_expr env in_main const real_arg) in
      (*Format.eprintf "subtyping const %B real %a:%a vs formal %a@." const Printers.pp_expr real_arg Types.print_ty real_type Types.print_ty formal_type;*)
      try_unify ~sub:sub formal_type real_type loc

    (* typing an application implies:
   - checking that const formal parameters match real const (maybe symbolic) arguments
   - checking type adequation between formal and real arguments
   An application may embed an homomorphic/internal function, in which case we need to split
   it in many calls
     *)
    and type_appl env in_main loc const f args =
      let targs = List.map (type_expr env in_main const) args in
      if Basic_library.is_homomorphic_fun f && List.exists is_tuple_type targs
      then
        try
          let targs = Utils.transpose_list (List.map type_list_of_type targs) in
          (* Types. *)type_of_type_list (List.map (type_simple_call env in_main loc const f) targs)
        with 
          Utils.TransposeError (l, l') -> raise (Error (loc, WrongMorphism (l, l')))
	                                
      else (
        type_dependent_call env in_main loc const f (List.combine args targs)
      )
      
    (* type a call with possible dependent types. [targs] is here a list of (argument, type) pairs. *)
    and type_dependent_call env in_main loc const f targs =
      (* Format.eprintf "Typing.type_dependent_call %s@." f; *)
      let tins, touts = new_var (), new_var () in
      (* Format.eprintf "tin=%a, tout=%a@." print_ty tins print_ty touts; *)
      let tfun = (* Type_predef. *)type_arrow tins touts in
      (* Format.eprintf "fun=%a@." print_ty tfun; *)
      type_subtyping_arg env in_main const (expr_of_ident f loc) tfun;
      (* Format.eprintf "type subtyping@."; *)
      let tins = type_list_of_type tins in
      if List.length targs <> List.length tins then
        raise (Error (loc, WrongArity (List.length tins, List.length targs)))
      else
        begin
          List.iter2 (
	      fun (a,t) ti ->
	      let t' = type_add_const env (const || (* Types. *)get_static_value ti <> None) a t in
	      (* Format.eprintf "uniying ti=%a t'=%a touts=%a@." print_ty ti print_ty t' print_ty touts;  *)
	      try_unify ~sub:true ti t' a.expr_loc;
	    (* Format.eprintf "unified ti=%a t'=%a touts=%a@." print_ty ti print_ty t' print_ty touts;  *)
	      
            )
	    targs
	    tins;
          touts
        end

    (* type a simple call without dependent types 
   but possible homomorphic extension.
   [targs] is here a list of arguments' types. *)
    and type_simple_call env in_main loc const f targs =
      let tins, touts = new_var (), new_var () in
      let tfun = (* Type_predef. *)type_arrow tins touts in
      type_subtyping_arg env in_main const (expr_of_ident f loc) tfun;
      (*Format.eprintf "try unify %a %a@." Types.print_ty tins Types.print_ty (type_of_type_list targs);*)
      try_unify ~sub:true tins (type_of_type_list targs) loc;
      touts

    (** [type_expr env in_main expr] types expression [expr] in environment
    [env], expecting it to be [const] or not. *)
    and type_expr ?(is_annot=false) env in_main const expr =
      let resulting_ty = 
        match expr.expr_desc with
        | Expr_const c ->
           let ty = type_const ~is_annot expr.expr_loc c in
           let ty = (* Type_predef. *)type_static (Dimension.mkdim_var ()) ty in
           expr.expr_type <- Expr_type_hub.export ty;
           ty
        | Expr_ident v ->
           let tyv =
             try
               Env.lookup_value (fst env) v
             with Not_found ->
	       Format.eprintf "Failure in typing expr %a. Not in typing environement@." Printers.pp_expr expr;
               raise (Error (expr.expr_loc, Unbound_value ("identifier " ^ v)))
           in
           let ty = instantiate (ref []) (ref []) tyv in
           let ty' =
             if const
             then (* Type_predef. *)type_static (Dimension.mkdim_var ()) (new_var ())
             else new_var () in
           try_unify ty ty' expr.expr_loc;
           expr.expr_type <- Expr_type_hub.export ty;
           ty 
        | Expr_array elist ->
           let ty_elt = new_var () in
           List.iter (fun e -> try_unify ty_elt (type_appl env in_main expr.expr_loc const "uminus" [e]) e.expr_loc) elist;
           let d = Dimension.mkdim_int expr.expr_loc (List.length elist) in
           let ty = (* Type_predef. *)type_array d ty_elt in
           expr.expr_type <- Expr_type_hub.export ty;
           ty
        | Expr_access (e1, d) ->
           type_subtyping_arg env in_main false (* not necessary a constant *) (expr_of_dimension d) (* Type_predef. *)type_int;
           let ty_elt = new_var () in
           let d = Dimension.mkdim_var () in
           type_subtyping_arg env in_main const e1 ((* Type_predef. *)type_array d ty_elt);
           expr.expr_type <- Expr_type_hub.export ty_elt;
           ty_elt
        | Expr_power (e1, d) ->
           let eval_const id = (* Types. *)get_static_value (Env.lookup_value (fst env) id) in
           type_subtyping_arg env in_main true (expr_of_dimension d) (* Type_predef. *)type_int;
           Dimension.eval Basic_library.eval_dim_env eval_const d;
           let ty_elt = type_appl env in_main expr.expr_loc const "uminus" [e1] in
           let ty = (* Type_predef. *)type_array d ty_elt in
           expr.expr_type <- Expr_type_hub.export ty;
           ty
        | Expr_tuple elist ->
           let ty = new_ty (Ttuple (List.map (type_expr ~is_annot env in_main const) elist)) in
           expr.expr_type <- Expr_type_hub.export ty;
           ty
        | Expr_ite (c, t, e) ->
           type_subtyping_arg env in_main const c (* Type_predef. *)type_bool;
           let ty = type_appl env in_main expr.expr_loc const "+" [t; e] in
           expr.expr_type <- Expr_type_hub.export ty;
           ty
        | Expr_appl (id, args, r) ->
           (* application of non internal function is not legal in a constant
       expression *)
           (match r with
            | None        -> ()
            | Some c -> 
               check_constant expr.expr_loc const false;	
               type_subtyping_arg env in_main const c (* Type_predef. *)type_bool);
           let args_list = expr_list_of_expr args in
           let touts = type_appl env in_main expr.expr_loc const id args_list in
           let targs = new_ty (Ttuple (List.map (fun a -> Expr_type_hub.import a.expr_type) args_list)) in
           args.expr_type <- Expr_type_hub.export targs;
           expr.expr_type <- Expr_type_hub.export touts;
           touts
        | Expr_fby (e1,e2)
          | Expr_arrow (e1,e2) ->
           (* fby/arrow is not legal in a constant expression *)
           check_constant expr.expr_loc const false;
           let ty = type_appl env in_main expr.expr_loc const "+" [e1; e2] in
           expr.expr_type <- Expr_type_hub.export ty;
           ty
        | Expr_pre e ->
           (* pre is not legal in a constant expression *)
           check_constant expr.expr_loc const false;
           let ty = type_appl env in_main expr.expr_loc const "uminus" [e] in
           expr.expr_type <- Expr_type_hub.export ty;
           ty
        | Expr_when (e1,c,l) ->
           (* when is not legal in a constant expression *)
           check_constant expr.expr_loc const false;
           let typ_l = (* Type_predef. *)type_clock (type_const ~is_annot expr.expr_loc (Const_tag l)) in
           let expr_c = expr_of_ident c expr.expr_loc in
           type_subtyping_arg env in_main ~sub:false const expr_c typ_l;
           let ty = type_appl env in_main expr.expr_loc const "uminus" [e1] in
           expr.expr_type <- Expr_type_hub.export ty;
           ty
        | Expr_merge (c,hl) ->
           (* merge is not legal in a constant expression *)
           check_constant expr.expr_loc const false;
           let typ_in, typ_out = type_branches env in_main expr.expr_loc const hl in
           let expr_c = expr_of_ident c expr.expr_loc in
           let typ_l = (* Type_predef. *)type_clock typ_in in
           type_subtyping_arg env in_main ~sub:false const expr_c typ_l;
           expr.expr_type <- Expr_type_hub.export typ_out;
           typ_out
      in 
      Log.report ~level:3 (fun fmt -> Format.fprintf fmt "Type of expr %a: %a@." Printers.pp_expr expr (* Types. *)print_ty resulting_ty);
      resulting_ty

    and type_branches ?(is_annot=false) env in_main loc const hl =
      let typ_in = new_var () in
      let typ_out = new_var () in
      try
        let used_labels =
          List.fold_left (fun accu (t, h) ->
	      unify typ_in (type_const ~is_annot loc (Const_tag t));
	      type_subtyping_arg env in_main const h typ_out;
	      if List.mem t accu
	      then raise (Error (loc, Already_bound t))
	      else t :: accu) [] hl in
        let type_labels = get_enum_type_tags (coretype_type typ_in) in
        if List.sort compare used_labels <> List.sort compare type_labels
        then let unbound_tag = List.find (fun t -> not (List.mem t used_labels)) type_labels in
	     raise (Error (loc, Unbound_value ("branching tag " ^ unbound_tag)))
        else (typ_in, typ_out)
      with Unify (t1, t2) ->
        raise (Error (loc, Type_clash (t1,t2)))

    (* Eexpr are always in annotations. TODO: add the quantifiers variables to the env *)
    let type_eexpr env eexpr = 
      (type_expr
         ~is_annot:true
         env
         false (* not in main *)
         false (* not a const *)
         eexpr.eexpr_qfexpr)


    (** [type_eq env eq] types equation [eq] in environment [env] *)
    let type_eq env in_main undefined_vars eq =
      (*Format.eprintf "Typing.type_eq %a@." Printers.pp_node_eq eq;*)
      (* Check undefined variables, type lhs *)
      let expr_lhs = expr_of_expr_list eq.eq_loc (List.map (fun v -> expr_of_ident v eq.eq_loc) eq.eq_lhs) in
      let ty_lhs = type_expr env in_main false expr_lhs in
      (* Check multiple variable definitions *)
      let define_var id uvars =
        if ISet.mem id uvars
        then ISet.remove id uvars
        else raise (Error (eq.eq_loc, Already_defined id))
      in
      (* check assignment of declared constant, assignment of clock *)
      let ty_lhs =
        type_of_type_list
          (List.map2 (fun ty id ->
	       if get_static_value ty <> None
	       then raise (Error (eq.eq_loc, Assigned_constant id)) else
	         match get_clock_base_type ty with
	         | None -> ty
	         | Some ty -> ty)
	     (type_list_of_type ty_lhs) eq.eq_lhs) in
      let undefined_vars =
        List.fold_left (fun uvars v -> define_var v uvars) undefined_vars eq.eq_lhs in
      (* Type rhs wrt to lhs type with subtyping, i.e. a constant rhs value may be assigned
     to a (always non-constant) lhs variable *)
      type_subtyping_arg env in_main false eq.eq_rhs ty_lhs;
      undefined_vars


    (* [type_coreclock env ck id loc] types the type clock declaration [ck]
   in environment [env] *)
    let type_coreclock env ck id loc =
      match ck.ck_dec_desc with
      | Ckdec_any -> ()
      | Ckdec_bool cl ->
         let dummy_id_expr = expr_of_ident id loc in
         let when_expr =
           List.fold_left
             (fun expr (x, l) ->
               {expr_tag = new_tag ();
                expr_desc= Expr_when (expr,x,l);
                expr_type = Types.Main.new_var ();
                expr_clock = Clocks.new_var true;
                expr_delay = Delay.new_var ();
                expr_loc=loc;
		expr_annot = None})
             dummy_id_expr cl
         in
         ignore (type_expr env false false when_expr)

    let rec check_type_declaration loc cty =
      match cty with
      | Tydec_clock ty
        | Tydec_array (_, ty) -> check_type_declaration loc ty
      | Tydec_const tname   ->
         (* Format.eprintf "TABLE: %a@." print_type_table (); *)
         if not (Hashtbl.mem type_table cty)
         then raise (Error (loc, Unbound_type tname));
      | _                   -> ()

    let type_var_decl vd_env env vdecl =
      (*Format.eprintf "Typing.type_var_decl START %a:%a@." Printers.pp_var vdecl Printers.print_dec_ty vdecl.var_dec_type.ty_dec_desc;*)
      check_type_declaration vdecl.var_loc vdecl.var_dec_type.ty_dec_desc;
      let eval_const id = (* Types. *)get_static_value (Env.lookup_value env id) in
      let type_dim d =
        begin
          type_subtyping_arg (env, vd_env) false true (expr_of_dimension d) (* Type_predef. *)type_int;
          Dimension.eval Basic_library.eval_dim_env eval_const d;
        end in
      let ty = type_coretype type_dim vdecl.var_dec_type.ty_dec_desc in

      let ty_static =
        if vdecl.var_dec_const
        then (* Type_predef. *)type_static (Dimension.mkdim_var ()) ty
        else ty in
      (match vdecl.var_dec_value with
       | None   -> ()
       | Some v -> type_subtyping_arg (env, vd_env) false ~sub:false true v ty_static);
      try_unify ty_static (Expr_type_hub.import vdecl.var_type) vdecl.var_loc;
      let new_env = Env.add_value env vdecl.var_id ty_static in
      type_coreclock (new_env,vd_env) vdecl.var_dec_clock vdecl.var_id vdecl.var_loc;
      (*Format.eprintf "END %a@." Types.print_ty ty_static;*)
      new_env

    let type_var_decl_list vd_env env l =
      List.fold_left (type_var_decl vd_env) env l

    let type_of_vlist vars =
      let tyl = List.map (fun v -> Expr_type_hub.import v.var_type) vars in
      type_of_type_list tyl

    let add_vdecl vd_env vdecl =
      if List.exists (fun v -> v.var_id = vdecl.var_id) vd_env
      then raise (Error (vdecl.var_loc, Already_bound vdecl.var_id))
      else vdecl::vd_env

    let check_vd_env vd_env =
      ignore (List.fold_left add_vdecl [] vd_env)

    let type_contract env c =
      let vd_env = c.consts @ c.locals in
      check_vd_env vd_env;
      let env = type_var_decl_list ((* this argument seems useless to me, cf TODO at top of the file*) vd_env) env vd_env in
      (* typing stmts *)
      let eqs = List.map (fun s -> match s with Eq eq -> eq | _ -> assert false) c.stmts  in
      let undefined_vars_init =
        List.fold_left
          (fun uvs v -> ISet.add v.var_id uvs)
          ISet.empty c.locals
      in
      let _ =
        List.fold_left
          (type_eq (env, vd_env) (false (*is_main*)))
          undefined_vars_init
          eqs
      in
      (* Typing each predicate expr *)
      let type_pred_ee ee : unit=
        type_subtyping_arg (env, vd_env) (false (* not in main *)) (false (* not a const *)) ee.eexpr_qfexpr type_bool
      in
      List.iter type_pred_ee
        (
          c.assume 
          @ c.guarantees
          @ List.flatten (List.map (fun m -> m.ensure @ m.require) c.modes) 
        );
      (*TODO 
        enrich env locally with locals and consts
        type each pre/post as a boolean expr
        I don't know if we want to update the global env with locally typed variables. 
        For the moment, returning the provided env           
       *)
      env

    let rec type_spec env spec loc =
      match spec with
      | Contract c -> type_contract env c
      | NodeSpec id -> env
                     
    (** [type_node env nd loc] types node [nd] in environment env. The
    location is used for error reports. *)
    and type_node env nd loc =
      (* Format.eprintf "Typing node %s@." nd.node_id; *)
      let is_main = nd.node_id = !Options.main_node in
      (* In contracts, outputs are considered as input values *)
      let vd_env_ol = if nd.node_iscontract then nd.node_locals else nd.node_outputs@nd.node_locals in
      let vd_env =  nd.node_inputs@nd.node_outputs@nd.node_locals in
      check_vd_env vd_env;
      let init_env = env in
      let delta_env = type_var_decl_list vd_env init_env nd.node_inputs in
      let delta_env = type_var_decl_list vd_env delta_env nd.node_outputs in
      let delta_env = type_var_decl_list vd_env delta_env nd.node_locals in
      let new_env = Env.overwrite env delta_env in
      let undefined_vars_init =
        List.fold_left
          (fun uvs v -> ISet.add v.var_id uvs)
          ISet.empty vd_env_ol in
      let undefined_vars =
        let eqs, auts = get_node_eqs nd in
        (* TODO XXX: il faut typer les handlers de l'automate *)
        List.fold_left (type_eq (new_env, vd_env) is_main) undefined_vars_init eqs
      in
      (* Typing asserts *)
      List.iter (fun assert_ ->
          let assert_expr =  assert_.assert_expr in
          type_subtyping_arg (new_env, vd_env) is_main false assert_expr (* Type_predef. *)type_bool
        )  nd.node_asserts;
      (* Typing spec/contracts *)
      (match nd.node_spec with
       | None -> ()
       | Some spec -> ignore (type_spec new_env spec loc));
      (* Typing annots *)
      List.iter (fun annot ->
          List.iter (fun (_, eexpr) -> ignore (type_eexpr (new_env, vd_env) eexpr)) annot.annots
        ) nd.node_annot;
      
      (* check that table is empty *)
      let local_consts = List.fold_left (fun res vdecl -> if vdecl.var_dec_const then ISet.add vdecl.var_id res else res) ISet.empty nd.node_locals in
      let undefined_vars = ISet.diff undefined_vars local_consts in
      
      if (not (ISet.is_empty undefined_vars)) then
        raise (Error (loc, Undefined_var undefined_vars));
      let ty_ins = type_of_vlist nd.node_inputs in
      let ty_outs = type_of_vlist nd.node_outputs in
      let ty_node = new_ty (Tarrow (ty_ins,ty_outs)) in
      generalize ty_node;
      (* TODO ? Check that no node in the hierarchy remains polymorphic ? *)
      nd.node_type <- Expr_type_hub.export ty_node;
      Env.add_value env nd.node_id ty_node

    let type_imported_node env nd loc =
      let vd_env = nd.nodei_inputs@nd.nodei_outputs in
      check_vd_env vd_env;
      let delta_env = type_var_decl_list vd_env env nd.nodei_inputs in
      let delta_env = type_var_decl_list vd_env delta_env nd.nodei_outputs in
      let new_env = Env.overwrite env delta_env in
      (* Typing spec *)
      (match nd.nodei_spec with
       | None -> ()
       | Some spec -> ignore (type_spec new_env spec loc)); 
      let ty_ins = type_of_vlist nd.nodei_inputs in
      let ty_outs = type_of_vlist nd.nodei_outputs in
      let ty_node = new_ty (Tarrow (ty_ins,ty_outs)) in
      generalize ty_node;
      (*
  if (is_polymorphic ty_node) then
    raise (Error (loc, Poly_imported_node nd.nodei_id));
       *)
      let new_env = Env.add_value env nd.nodei_id ty_node in
      nd.nodei_type <- Expr_type_hub.export ty_node;
      new_env

    let type_top_const env cdecl =
      let ty = type_const cdecl.const_loc cdecl.const_value in
      let d =
        if is_dimension_type ty
        then dimension_of_const cdecl.const_loc cdecl.const_value
        else Dimension.mkdim_var () in
      let ty = (* Type_predef. *)type_static d ty in
      let new_env = Env.add_value env cdecl.const_id ty in
      cdecl.const_type <- Expr_type_hub.export ty;
      new_env

    let type_top_consts env clist =
      List.fold_left type_top_const env clist

    let rec type_top_decl env decl =
      match decl.top_decl_desc with
      | Node nd -> (
        try
          type_node env nd decl.top_decl_loc
        with Error (loc, err) as exc -> (
          if !Options.global_inline then
	    Format.eprintf "Type error: failing node@.%a@.@?"
	      Printers.pp_node nd
          ;
            raise exc)
      )
      | ImportedNode nd ->
         type_imported_node env nd decl.top_decl_loc
      | Const c ->
         type_top_const env c
      | TypeDef _ -> List.fold_left type_top_decl env (consts_of_enum_type decl)
      | Include _ | Open _  -> env
    
    let get_type_of_call decl =
      match decl.top_decl_desc with
      | Node nd         ->
         let (in_typ, out_typ) = split_arrow (Expr_type_hub.import nd.node_type) in
         type_list_of_type in_typ, type_list_of_type out_typ
      | ImportedNode nd ->
         let (in_typ, out_typ) = split_arrow (Expr_type_hub.import nd.nodei_type) in
         type_list_of_type in_typ, type_list_of_type out_typ
      | _               -> assert false

    let type_prog env decls =
      try
        List.fold_left type_top_decl env decls
      with Failure _ as exc -> raise exc

    (* Once the Lustre program is fully typed, we must get back to the
       original description of dimensions, with constant parameters,
       instead of unifiable internal variables. *)

    (* The following functions aims at 'unevaluating' dimension
       expressions occuring in array types, i.e. replacing unifiable
       second_order variables with the original static parameters.
       Once restored in this formulation, dimensions may be
       meaningfully printed.  *)
    let uneval_vdecl_generics vdecl =
      if vdecl.var_dec_const
      then
        match get_static_value (Expr_type_hub.import vdecl.var_type) with
        | None   -> (Format.eprintf "internal error: %a@." (* Types. *)print_ty (Expr_type_hub.import vdecl.var_type); assert false)
        | Some d -> Dimension.uneval vdecl.var_id d

    let uneval_node_generics vdecls =
      List.iter uneval_vdecl_generics vdecls

    let uneval_spec_generics spec =
      List.iter uneval_vdecl_generics (spec.consts@spec.locals)
      
    let uneval_top_generics decl =
      match decl.top_decl_desc with
      | Node nd ->
         uneval_node_generics (nd.node_inputs @ nd.node_outputs)
      | ImportedNode nd ->
         uneval_node_generics (nd.nodei_inputs @ nd.nodei_outputs)
      | Const _ | TypeDef _ | Open _ | Include _ 
        -> ()

    let uneval_prog_generics prog =
      List.iter uneval_top_generics prog

    let rec get_imported_symbol decls id =
      match decls with
      | [] -> assert false
      | decl::q ->
         (match decl.top_decl_desc with
          | ImportedNode nd when id = nd.nodei_id && decl.top_decl_itf -> decl
          | Const c when id = c.const_id && decl.top_decl_itf -> decl
          | TypeDef _ -> get_imported_symbol (consts_of_enum_type decl @ q) id
          | _ -> get_imported_symbol q id)

    let check_env_compat header declared computed = 
      uneval_prog_generics header;
      Env.iter declared (fun k decl_type_k ->
          let top = get_imported_symbol header k in
          let loc = top.top_decl_loc in 
          try
            let computed_t = Env.lookup_value computed k in
            let computed_t = instantiate (ref []) (ref []) computed_t in
            (*Types.print_ty Format.std_formatter decl_type_k;
              Types.print_ty Format.std_formatter computed_t;*)                   
            try_unify ~sub:true ~semi:true decl_type_k computed_t loc
          with Not_found ->
            begin
              (* If top is a contract we do not require the lustre
                 file to provide the same definition. *)
              match top.top_decl_desc with
              | Node nd -> (
                match nd.node_spec with
                | Some (Contract _) -> ()
                | _ -> raise (Error (loc, Declared_but_undefined k))
              )                                                            
              | _ ->
                 raise (Error (loc, Declared_but_undefined k))
            end
        )

    let check_typedef_top decl =
      (*Format.eprintf "check_typedef %a@." Printers.pp_short_decl decl;*)
      (*Format.eprintf "%a" Printers.pp_typedef (typedef_of_top decl);*)
      (*Format.eprintf "%a" Corelang.print_type_table ();*)
      match decl.top_decl_desc with
      | TypeDef ty ->
         let owner = decl.top_decl_owner in
         let itf = decl.top_decl_itf in
         let decl' =
           try Hashtbl.find type_table (Tydec_const (typedef_of_top decl).tydef_id)
           with Not_found -> raise (Error (decl.top_decl_loc, Declared_but_undefined ("type "^ ty.tydef_id))) in
         let owner' = decl'.top_decl_owner in
         (*Format.eprintf "def owner = %s@.decl owner = %s@." owner' owner;*)
         let itf' = decl'.top_decl_itf in
         (match decl'.top_decl_desc with
          | Const _ | Node _ | ImportedNode _ -> assert false
          | TypeDef ty' when coretype_equal ty'.tydef_desc ty.tydef_desc && owner' = owner && itf && (not itf') -> ()
          | _ -> raise (Error (decl.top_decl_loc, Type_mismatch ty.tydef_id)))
      | _  -> ()

    let check_typedef_compat header =
      List.iter check_typedef_top header
  end

include  Make(Types.Main) (struct
             type type_expr  = Types.Main.type_expr
             let import x = x
             let export x = x
           end)
             (* Local Variables: *)
             (* compile-command:"make -C .." *)
(* End: *)
