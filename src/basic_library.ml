(********************************************************************)
(*                                                                  *)
(*  The LustreC compiler toolset   /  The LustreC Development Team  *)
(*  Copyright 2012 -    --   ONERA - CNRS - INPT - LIFL             *)
(*                                                                  *)
(*  LustreC is free software, distributed WITHOUT ANY WARRANTY      *)
(*  under the terms of the GNU Lesser General Public License        *)
(*  version 2.1.                                                    *)
(*                                                                  *)
(********************************************************************)

(* Parts of this file come from the Prelude compiler *)

(*open LustreSpec*)
open Type_predef
open Clock_predef
open Delay_predef
open Dimension

module TE = Env

let static_op ty =
  type_static (mkdim_var ()) ty

let type_env =
  List.fold_left
    (fun env (op, op_type) -> TE.add_value env op op_type)
    TE.initial
    [
      "true", (static_op type_bool);
      "false", (static_op type_bool);
      "+", (static_op type_bin_poly_op);
      "uminus", (static_op type_unary_poly_op);
      "-", (static_op type_bin_poly_op);
      "*", (static_op type_bin_poly_op);
      "/", (static_op type_bin_poly_op);
      "mod", (static_op type_bin_int_op);
      "&&", (static_op type_bin_bool_op);
      "||", (static_op type_bin_bool_op);
      "xor", (static_op type_bin_bool_op);
      "equi", (static_op type_bin_bool_op);
      "impl", (static_op type_bin_bool_op);
      "<", (static_op type_bin_comp_op);
      "<=", (static_op type_bin_comp_op);
      ">", (static_op type_bin_comp_op);
      ">=", (static_op type_bin_comp_op);
      "!=", (static_op type_bin_comp_op);
      "=", (static_op type_bin_comp_op);
      "not", (static_op type_unary_bool_op)
]

module CE = Env

let clock_env =
  let init_env = CE.initial in
  let env' =
    List.fold_right (fun op env -> CE.add_value env op ck_nullary_univ)
      ["true"; "false"] init_env in
  let env' =
    List.fold_right (fun op env -> CE.add_value env op ck_unary_univ)
      ["uminus"; "not"] env' in
  let env' =
    List.fold_right (fun op env -> CE.add_value env op ck_bin_univ)
      ["+"; "-"; "*"; "/"; "mod"; "&&"; "||"; "xor"; "equi"; "impl"; "<"; "<="; ">"; ">="; "!="; "="] env' in
  env'

module DE = Env

let delay_env =
  let init_env = DE.initial in
  let env' =
    List.fold_right (fun op env -> DE.add_value env op delay_nullary_poly_op)
      ["true"; "false"] init_env in
  let env' =
    List.fold_right (fun op env -> DE.add_value env op delay_unary_poly_op)
      ["uminus"; "not"] env' in
  let env' =
    List.fold_right (fun op env -> DE.add_value env op delay_binary_poly_op)
      ["+"; "-"; "*"; "/"; "mod"; "&&"; "||"; "xor"; "equi"; "impl"; "<"; "<="; ">"; ">="; "!="; "="] env' in
  let env' =
    List.fold_right (fun op env -> DE.add_value env op delay_ternary_poly_op)
      [] env' in
  env'

module VE = Env

let eval_dim_env =
  let defs = [
    "uminus", (function [Dint a] -> Dint (-a)           | _ -> assert false);
    "not", (function [Dbool b] -> Dbool (not b)         | _ -> assert false);
    "+", (function [Dint a; Dint b] -> Dint (a+b)       | _ -> assert false);
    "-", (function [Dint a; Dint b] -> Dint (a-b)       | _ -> assert false);
    "*", (function [Dint a; Dint b] -> Dint (a*b)       | _ -> assert false);
    "/", (function [Dint a; Dint b] -> Dint (a/b)       | _ -> assert false);
    "mod", (function [Dint a; Dint b] -> Dint (a mod b) | _ -> assert false);
    "&&", (function [Dbool a; Dbool b] -> Dbool (a&&b)  | _ -> assert false);
    "||", (function [Dbool a; Dbool b] -> Dbool (a||b)  | _ -> assert false);
    "xor", (function [Dbool a; Dbool b] -> Dbool (a<>b) | _ -> assert false);
    "equi", (function [Dbool a; Dbool b] -> Dbool (a=b) | _ -> assert false);
    "impl", (function [Dbool a; Dbool b] -> Dbool (a<=b)| _ -> assert false);
    "<", (function [Dint a; Dint b] -> Dbool (a<b)      | _ -> assert false);
    ">", (function [Dint a; Dint b] -> Dbool (a>b)      | _ -> assert false);
    "<=", (function [Dint a; Dint b] -> Dbool (a<=b)    | _ -> assert false);
    ">=", (function [Dint a; Dint b] -> Dbool (a>=b)    | _ -> assert false);
    "!=", (function [a; b] -> Dbool (a<>b)              | _ -> assert false);
    "=", (function [a; b] -> Dbool (a=b)                | _ -> assert false);
  ]
  in
  List.fold_left
    (fun env (op, op_eval) -> VE.add_value env op op_eval)
    VE.initial
    defs

let arith_funs = ["+";"-";"*";"/";"mod"; "uminus"]
let bool_funs  = ["&&";"||";"xor";"equi";"impl"; "not"]
let rel_funs   = ["<";">";"<=";">=";"!=";"="]

let internal_funs = arith_funs@bool_funs@rel_funs
 
let rec is_internal_fun x targs =
(*Format.eprintf "is_internal_fun %s %a@." x Types.print_ty (List.hd targs);*)
  match targs with
  | []                              -> assert false
  | t::_ when Types.is_real_type t  -> List.mem x internal_funs && not !Options.mpfr 
  | t::_ when Types.is_array_type t -> is_internal_fun x [Types.array_element_type t]
  | _                               -> List.mem x internal_funs

let is_expr_internal_fun expr =
  let open Lustre_types in
  match expr.expr_desc with
  | Expr_appl (f, e, _) -> is_internal_fun f (Types.type_list_of_type e.expr_type)
  | _                   -> assert false

let is_value_internal_fun v =
  let open Machine_code_types in
  match v.value_desc with
  | Fun (f, vl) -> is_internal_fun f (List.map (fun v -> v.value_type) vl)
  | _           -> assert false

let is_numeric_operator x =
  List.mem x arith_funs

let is_homomorphic_fun x =
  List.mem x internal_funs

let is_stateless_fun x =
  List.mem x internal_funs


(* let pp_java i pp_val fmt vl = *)
(*   match i, vl with *)
(*   (\*  | "ite", [v1; v2; v3] -> Format.fprintf fmt "(%a?(%a):(%a))" pp_val v1 pp_val v2 pp_val v3 *\) *)
(*     | "uminus", [v] -> Format.fprintf fmt "(- %a)" pp_val v *)
(*     | "not", [v] -> Format.fprintf fmt "(!%a)" pp_val v *)
(*     | "impl", [v1; v2] -> Format.fprintf fmt "(!%a || %a)" pp_val v1 pp_val v2 *)
(*     | "=", [v1; v2] -> Format.fprintf fmt "(%a == %a)" pp_val v1 pp_val v2 *)
(*     | "mod", [v1; v2] -> Format.fprintf fmt "(%a %% %a)" pp_val v1 pp_val v2 *)
(*     | "equi", [v1; v2] -> Format.fprintf fmt "(%a == %a)" pp_val v1 pp_val v2 *)
(*     | "xor", [v1; v2] -> Format.fprintf fmt "(%a != %a)" pp_val v1 pp_val v2 *)
(*     | _, [v1; v2] -> Format.fprintf fmt "(%a %s %a)" pp_val v1 i pp_val v2 *)
(*     | _ -> (Format.eprintf "internal error: Basic_library.pp_java %s@." i; assert false) *)

let rec partial_eval op e opt =
  let open Lustre_types in
  let is_zero e =
    match e.expr_desc with
    | Expr_const (Const_int 0) -> true
    | Expr_const (Const_real r) when Real.is_zero r -> true
    | _ -> false
  in
  let is_one e =
    match e.expr_desc with
    | Expr_const (Const_int 1) -> true
    | Expr_const (Const_real r) when Real.is_one r -> true
    | _ -> false
  in
  let is_true, is_false =
    let is_tag t e = e.expr_desc = Expr_const (Const_tag t) in
    is_tag tag_true, is_tag tag_false
  in
  let int_arith_op, real_arith_op=
    let assoc op=
      match op with
      | "+" -> (+), Real.add
      | "-" -> (-), Real.minus
      | "*" -> ( * ), Real.times
      | "/" -> (/), Real.div
      | "mod" -> (mod), (fun _ _ -> assert false)
      | _ -> assert false  
    in
    (fun op -> fst(assoc op)), (fun op -> snd(assoc op))
  in
  let int_rel_op, real_rel_op =
    let assoc op =
      match op with
      | "<" -> (<), Real.lt
      |">" -> (>), Real.gt
      |"<="-> (<=), Real.le
      | ">=" -> (>=), Real.ge
      |"!=" -> (!=), Real.diseq
      |"=" -> (=), Real.eq
      | _ -> assert false
    in
    (fun op -> fst(assoc op)), (fun op -> snd(assoc op))
  in
  let eval_bool_fun op e1 e2  =
    let s2b s = if s= tag_true then true else if s=tag_false then false else assert false in
    let e1, e2 = s2b e1, s2b e2 in
    let r =
      match op with
      "&&" -> e1 && e2
    | "||" -> e1 || e2
    | "xor" -> (e1 && e2) || ((not e1) && (not e2)) 
    | "impl" -> (not e1) || e2
    | "equi" -> ((not e1) || e2) && ((not e2) || e1)
    | _ -> assert false
    in
    if r then Const_tag tag_true else Const_tag tag_false
    in
  let is_const e =
    match e.expr_desc with Expr_const _ -> true | _ -> false
  in
  let deconst e =
    match e.expr_desc with
    | Expr_const c -> c
    | _ -> assert false
  in
  match op, (match  e.expr_desc with Expr_tuple el -> el | _ -> [e]) with
  | _, el when List.for_all is_const el -> (
    let new_cst = 
      match op, List.map deconst el with
      | ("+"|"-"|"*"|"/"|"mod"), [Const_int c1; Const_int c2] ->
          Const_int (int_arith_op op c1 c2)
      | ("+"|"-"|"*"|"/"), [Const_real c1; Const_real c2] ->
         Const_real (real_arith_op op c1 c2)
      | "uminus", [Const_int c] -> Const_int (-c)
      | "uminus", [Const_real c] -> Const_real (Real.uminus c)
      | rel_fun, [Const_int c1; Const_int c2]
           when List.mem rel_fun rel_funs ->
         if int_rel_op op c1 c2 then
           Const_tag tag_true
         else
           Const_tag tag_false
      | rel_fun, [Const_real c1; Const_real c2]
           when List.mem rel_fun rel_funs ->
         if real_rel_op op c1 c2 then
           Const_tag tag_true
         else
           Const_tag tag_false
      | "=", [Const_tag t1; Const_tag t2]
             ->
         if t1 = t2 then
           Const_tag tag_true
         else
           Const_tag tag_false
      | "!=", [Const_tag t1; Const_tag t2]
             ->
         if t1 = t2 then
           Const_tag tag_false
         else
           Const_tag tag_true
      | "not", [Const_tag c] -> Const_tag( if c = tag_true then tag_false else if c = tag_false then tag_true else assert false)
      | bool_fun, [Const_tag c1; Const_tag c2]
           when List.mem bool_fun bool_funs ->
         eval_bool_fun bool_fun c1 c2 
      | _ -> let loc= e.expr_loc in
             let err =Error.Unbound_symbol (op ^ (string_of_bool (List.mem op rel_funs)) ^ " in basic library") in
             raise (Error.Error (loc, err))
    in
    Expr_const new_cst 
  )       
  | op, el -> ( (* at least one of the arguments is non constant *)
    match op, el with
    | "+", [e0; e] when is_zero e0 ->
       e.expr_desc
    | "+", [e; e0] when is_zero e0 ->
       e.expr_desc
    | "-", [e; e0] when is_zero e0 ->
       e.expr_desc
    | "-", [e0; e] when is_zero e0 ->
       Expr_appl("uminus", e, None)
    | ("*"|"/"), [e0; e] when is_zero e0 -> e0.expr_desc
    | "*", [e; e0] when is_zero e0 -> e0.expr_desc
    | "*", [e1; e] when is_one e1 -> e.expr_desc
    | "/", [e; e1] when is_one e1 -> e.expr_desc
    | "&&", [efalse; _] when is_false efalse ->
       Expr_const (Const_tag tag_false)
    | "&&", [_; efalse] when is_false efalse ->
       Expr_const (Const_tag tag_false)
    | "||", [etrue; _] when is_true etrue ->
       Expr_const (Const_tag tag_true)
    | "||", [_; etrue] when is_true etrue ->
       Expr_const (Const_tag tag_true)
    | "impl", [efalse; _] when is_false efalse ->
       Expr_const (Const_tag tag_true)
    | _ ->
       Expr_appl(op, e, opt)
                               )
                  (* Local Variables: *)
                  (* compile-command:"make -C .." *)
                  (* End: *)


let _ =
  (* Loading environement *)
  Global.type_env := type_env;
  Global.clock_env := clock_env
