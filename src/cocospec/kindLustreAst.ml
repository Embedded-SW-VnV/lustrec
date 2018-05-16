(* This file is part of the Kind 2 model checker.

   Copyright (c) 2015 by the Board of Trustees of the University of Iowa

   Licensed under the Apache License, Version 2.0 (the "License"); you
   may not use this file except in compliance with the License.  You
   may obtain a copy of the License at

   http://www.apache.org/licenses/LICENSE-2.0 

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or
   implied. See the License for the specific language governing
   permissions and limitations under the License. 

*)

open KindLib
module Log = KindLog
               
module SI = Set.Make (KindIdent)

exception Parser_error


let error_at_position pos msg =
  match Log.get_log_format () with
  | Log.F_pt ->
    Log.log L_error "Parser error at %a: %s" KindLib.pp_print_position pos msg
  | Log.F_xml -> Log.parse_log_xml L_error pos msg
  | Log.F_json -> Log.parse_log_json L_error pos msg
  | Log.F_relay -> ()


let warn_at_position pos msg = 
  match Log.get_log_format () with
  | Log.F_pt ->
    Log.log L_warn "Parser warning at %a: %s" KindLib.pp_print_position pos msg
  | Log.F_xml -> Log.parse_log_xml L_warn pos msg
  | Log.F_json -> Log.parse_log_json L_warn pos msg
  | Log.F_relay -> ()


(* ********************************************************************** *)
(* Type declarations                                                      *)
(* ********************************************************************** *)


(* An identifier *)
type ident = string

type index = string

let pp_print_ident = Format.pp_print_string

let pp_print_index = Format.pp_print_string


(* A clock expression *)
type clock_expr =
  | ClockTrue
  | ClockPos of ident
  | ClockNeg of ident
  | ClockConstr of ident * ident


(* A Lustre expression *)
type expr =

  (* Identifier *)
  | Ident of position * ident
  | ModeRef of position * ident list
  | RecordProject of position * expr * index
  | TupleProject of position * expr * expr

  (* Update of an indexed expression *)
  | StructUpdate of position * expr * label_or_index list * expr

  (* Values *)
  | True of position
  | False of position
  | Num of position * string
  | Dec of position * string

  (* Conversions *)
  | ToInt of position * expr
  | ToReal of position * expr

  (* List of expressions *)
  | ExprList of position * expr list 

  (* Tuple expression *)
  | TupleExpr of position * expr list 

  (* Array expression *)
  | ArrayExpr of position * expr list 

  (* Array expression *)
  | ArrayConstr of position * expr * expr 

  (* Slice of array *)
  | ArraySlice of position * expr * (expr * expr) 

  (* Array concatenation *)
  | ArrayConcat of position * expr * expr

  (* Record expression *)
  | RecordExpr of position * ident * (ident * expr) list

  (* Boolean operators *)
  | Not of position * expr 
  | And of position * expr * expr 
  | Or of position * expr * expr
  | Xor of position * expr * expr 
  | Impl of position * expr * expr 
  | Forall of position * typed_ident list * expr
  | Exists of position * typed_ident list * expr
  | OneHot of position * expr list

  (* Arithmetic operators *)
  | Uminus of position * expr 
  | Mod of position * expr * expr
  | Minus of position * expr * expr
  | Plus of position * expr * expr
  | Div of position * expr * expr
  | Times of position * expr * expr
  | IntDiv of position * expr * expr

  (* If operator *)
  | Ite of position * expr * expr * expr 

  (* With operator for recursive definitions *)
  | With of position * expr * expr * expr 

  (* Relations *)
  | Eq of position * expr * expr 
  | Neq of position * expr * expr
  | Lte of position * expr * expr
  | Lt of position * expr * expr
  | Gte of position * expr * expr
  | Gt of position * expr * expr

  (* Clock operators *)
  | When of position * expr * clock_expr
  | Current of position * expr
  | Condact of position * expr * expr * ident * expr list * expr list
  | Activate of position * ident * expr * expr * expr list
  | Merge of position * ident * (ident * expr) list
  | RestartEvery of position * ident * expr list * expr
      
  (* Temporal operators *)
  | Pre of position * expr
  | Last of position * ident
  | Fby of position * expr * int * expr 
  | Arrow of position * expr * expr 

  (* A node call *)
  | Call of position * ident * expr list 

  (* A node call setting static parameters *)
  | CallParam of position * ident * lustre_type list * expr list 


(* A built-in type *)
and lustre_type =
  | Bool of position
  | Int of position
  | IntRange of position * expr * expr
  | Real of position
  | UserType of position * ident
  | TupleType of position * lustre_type list
  | RecordType of position * typed_ident list
  | ArrayType of position * (lustre_type * expr)
  | EnumType of position * ident option * ident list


(* A declaration of an unclocked type *)
and typed_ident = KindLib.position * ident * lustre_type

(* A record field or an array or tuple index *)
and label_or_index = 
  | Label of KindLib.position * index
  | Index of KindLib.position * expr

(* A declaration of a type *)
type type_decl = 
  | AliasType of position * ident * lustre_type  
  | FreeType of position * ident

(* A declaration of a clocked type *)
type clocked_typed_decl = 
  position * ident * lustre_type * clock_expr


(* A declaration of a clocked type *)
type const_clocked_typed_decl = 
  position * ident * lustre_type * clock_expr * bool


(* A declaration of a constant *)
type const_decl = 
  | FreeConst of position * ident * lustre_type
  | UntypedConst of position * ident * expr 
  | TypedConst of position * ident * expr * lustre_type

(*
(* A variable declaration *)
type var_decl = position * ident * lustre_type * clock_expr
*)

(* A static parameter of a node *)
type node_param =
  | TypeParam of ident


(* A local declaration in a node *)
type node_local_decl =
  | NodeConstDecl of position * const_decl 
  | NodeVarDecl of position * clocked_typed_decl


(* Structural assignment in left-hand side of equation *)
type struct_item =
  | SingleIdent of position * ident
  | TupleStructItem of position * struct_item list
  | TupleSelection of position * ident * expr
  | FieldSelection of position * ident * ident
  | ArraySliceStructItem of position * ident * (expr * expr) list
  | ArrayDef of position * ident * ident list


(* The left-hand side of an equation *)
type eq_lhs =
  | StructDef of position * struct_item list

type transition_to =
  | TransRestart of position * (position * ident)
  | TransResume of position * (position * ident)

type transition_branch =
  | Target of transition_to
  | TransIf of position * expr *
               transition_branch * transition_branch option
  
type automaton_transition = position * transition_branch

type auto_returns = Given of ident list | Inferred

(* An equation or assertion in the node body *)
type node_equation =
  | Assert of position * expr
  | Equation of position * eq_lhs * expr 
  | Automaton of position * ident option * state list * auto_returns


and state =
  | State of position * ident * bool *
             node_local_decl list *
             node_equation list *
             automaton_transition option *
             automaton_transition option


(* An item in a node declaration *)
type node_item =
  | Body of node_equation
  | AnnotMain of bool
  | AnnotProperty of position * string option * expr


(* A contract ghost constant. *)
type contract_ghost_const = const_decl

(* A contract ghost variable. *)
type contract_ghost_var = const_decl

(* A contract assume. *)
type contract_assume = position * string option * expr

(* A contract guarantee. *)
type contract_guarantee = position * string option * expr

(* A contract requirement. *)
type contract_require = position * string option * expr

(* A contract ensure. *)
type contract_ensure = position * string option * expr

(* A contract mode. *)
type contract_mode =
  position * ident * (contract_require list) * (contract_ensure list)

(* A contract call. *)
type contract_call = position * ident * expr list * expr list

(* Equations that can appear in a contract node. *)
type contract_node_equation =
  | GhostConst of contract_ghost_const
  | GhostVar of contract_ghost_var
  | Assume of contract_assume
  | Guarantee of contract_guarantee
  | Mode of contract_mode
  | ContractCall of contract_call

(* A contract is some ghost consts / var, and assumes guarantees and modes. *)
type contract = contract_node_equation list


(* A node or function declaration

Boolean flag indicates whether node / function is extern. *)
type node_decl =
  ident
  * bool
  * node_param list
  * const_clocked_typed_decl list
  * clocked_typed_decl list
  * node_local_decl list
  * node_item list
  * contract option

(* A contract node declaration. Almost the same as a [node_decl] but
   with a different type for equations, and no contract
   specification. *)
type contract_node_decl =
  ident
  * node_param list
  * const_clocked_typed_decl list
  * clocked_typed_decl list
  * contract


(* An instance of a parameterized node *)
type node_param_inst = ident * ident * lustre_type list
  
(* A declaration as parsed *)
type declaration = 
  | TypeDecl of position * type_decl
  | ConstDecl of position * const_decl
  | NodeDecl of position * node_decl
  | FuncDecl of position * node_decl
  | ContractNodeDecl of position * contract_node_decl
  | NodeParamInst of position * node_param_inst


(* A Lustre program *)
type t = declaration list


(* ********************************************************************** *)
(* Pretty-printing functions                                              *)
(* ********************************************************************** *)


(* Pretty-print a clock expression *)
let pp_print_clock_expr ppf = function
  | ClockTrue -> ()
  | ClockPos s -> Format.fprintf ppf "@ when %a" pp_print_ident s
  | ClockNeg s -> Format.fprintf ppf "@ when not %a" pp_print_ident s
  | ClockConstr (s, c) ->
    Format.fprintf ppf "@ when %a(%a)" pp_print_ident c pp_print_ident s


(* Pretty-print a Lustre expression *)
let rec pp_print_expr ppf = 

  let ppos ppf p =
    (if false then Format.fprintf else Format.ifprintf)
      ppf
      "%a" 
      pp_print_position p
  in

  (* Pretty-print a string *)
  let ps p = Format.fprintf ppf "%a%s" ppos p in 

  (* Pretty-print a unary operator *)
  let p1 p s e = 
    Format.fprintf ppf "@[<hv 2>%a(%s %a)@]" 
      ppos p 
      s 
      pp_print_expr e 
  in 

  (* Pretty-print a binary infix operator *)
  let p2 p s e1 e2 = 
    Format.fprintf ppf
      "@[<hv 2>%a(%a %s@ %a)@]" 
      ppos p 
      pp_print_expr e1 
      s 
      pp_print_expr e2 
  in 

  (* Pretty-print a ternary infix operator *)
  let p3 p s1 s2 s3 e1 e2 e3 = 
    Format.fprintf ppf
      "@[<hv 2>%a(%s@ %a@;<1 -1>%s@ %a@;<1 -1>%s@ %a)@]" 
      ppos p 
      s1 
      pp_print_expr e1 
      s2
      pp_print_expr e2 
      s3 
      pp_print_expr e3 
  in 
  
  (* Pretty-print a comma-separated list of expressions *)
  let rec pl ppf = function 
    | [] -> ()
    | [e] -> Format.fprintf ppf "%a" pp_print_expr e
    | e :: tl -> Format.fprintf ppf "%a,@ %a" pl [e] pl tl
  in

  (* Pretty-print a variadic prefix operator *)
  let pnp p s l = 
    Format.fprintf ppf
      "@[<hv 2>%a%s@,@[<hv 1>(%a)@]@]" 
      ppos p 
      s
      pl l
  in

  function
    
    | Ident (p, id) -> Format.fprintf ppf "%a%a" ppos p pp_print_ident id

    | ModeRef (p, ids) ->
      Format.fprintf ppf "%a::%a" ppos p (
        pp_print_list pp_print_ident "::"
      ) ids
 
    | ExprList (p, l) -> Format.fprintf ppf "%a@[<hv 1>(%a)@]" ppos p pl l

    | TupleExpr (p, l) -> Format.fprintf ppf "%a@[<hv 1>{%a}@]" ppos p pl l

    | ArrayExpr (p, l) -> Format.fprintf ppf "%a@[<hv 1>[%a]@]" ppos p pl l

    | StructUpdate (p, e1, i, e2) -> 

      Format.fprintf ppf
        "@[<hv 1>(%a@ with@ @[<hv>%a@] =@ %a)@]"
        pp_print_expr e1
        (pp_print_list pp_print_label_or_index "") i
        pp_print_expr e2


    | ArrayConstr (p, e1, e2) -> 

      Format.fprintf ppf 
        "%a@[<hv 1>(%a^%a)@]" 
        ppos p 
        pp_print_expr e1 
        pp_print_expr e2

    | ArraySlice (p, e, l) -> 

      Format.fprintf ppf 
        "%a@[<hv 1>%a@[<hv 1>[%a]@]@]" 
        ppos p 
        pp_print_expr e
        pp_print_array_slice l 

    | ArrayConcat (p, e1, e2) -> 

      Format.fprintf ppf 
        "%a@[<hv 1>%a|%a@]" 
        ppos p 
        pp_print_expr e1
        pp_print_expr e2 

    | RecordProject (p, e, f) -> 

      Format.fprintf ppf 
        "%a%a.%a" 
        ppos p 
        pp_print_expr e 
        pp_print_index f

    | RecordExpr (p, t, l) -> 

      Format.fprintf ppf 
        "%a@[<hv 1>%a {%a}@]" 
        ppos p 
        pp_print_ident t
        (pp_print_list pp_print_field_assign ";@ ") l

    | TupleProject (p, e, f) -> 

      Format.fprintf ppf "%a%a.%%%a" ppos p pp_print_expr e pp_print_expr f

    | True p -> ps p "true"
    | False p -> ps p "false"

    | Num (p, n) -> ps p n
    | Dec (p, d) -> ps p d

    | ToInt (p, e) -> p1 p "int" e
    | ToReal (p, e) -> p1 p "real" e

    | Not (p, e) -> p1 p "not" e
    | And (p, e1, e2) -> p2 p "and" e1 e2
    | Or (p, e1, e2) -> p2 p "or" e1 e2
    | Xor (p, e1, e2) -> p2 p "xor" e1 e2
    | Impl (p, e1, e2) -> p2 p "=>" e1 e2
    | OneHot (p, e) -> pnp p "#" e
    | Forall (pos, vars, e) -> 
      Format.fprintf ppf "@[<hv 2>forall@ @[<hv 1>(%a)@]@ %a@]" 
        (pp_print_list pp_print_typed_decl ";@ ") vars
        pp_print_expr e
    | Exists (pos, vars, e) -> 
      Format.fprintf ppf "@[<hv 2>exists@ @[<hv 1>(%a)@]@ %a@]" 
        (pp_print_list pp_print_typed_decl ";@ ") vars
        pp_print_expr e

    | Uminus (p, e) -> p1 p "-" e
    | Mod (p, e1, e2) -> p2 p "mod" e1 e2 
    | Minus (p, e1, e2) -> p2 p "-" e1 e2
    | Plus (p, e1, e2) -> p2 p "+" e1 e2
    | Div (p, e1, e2) -> p2 p "/" e1 e2
    | Times (p, e1, e2) -> p2 p "*" e1 e2
    | IntDiv (p, e1, e2) -> p2 p "div" e1 e2

    | Ite (p, e1, e2, e3) -> p3 p "if" "then" "else" e1 e2 e3

    | With (p, e1, e2, e3) -> p3 p "with" "then" "else" e1 e2 e3

    | Eq (p, e1, e2) -> p2 p "=" e1 e2
    | Neq (p, e1, e2) -> p2 p "<>" e1 e2
    | Lte (p, e1, e2) -> p2 p "<=" e1 e2
    | Lt (p, e1, e2) -> p2 p "<" e1 e2
    | Gte (p, e1, e2) -> p2 p ">=" e1 e2
    | Gt (p, e1, e2) -> p2 p ">" e1 e2

    | When (p, e1, e2) ->
      Format.fprintf ppf "%a %a when %a"
        ppos p
        pp_print_expr e1
        pp_print_clock_expr e2

    | Current (p, e) -> p1 p "current" e
    | Condact (p, e1, er, n, e2, e3) -> 
  
      Format.fprintf ppf 
        "%acondact(%a,restart %a,%a(%a),%a)" 
        ppos p
        pp_print_expr e1
        pp_print_expr er
        pp_print_ident n
        (pp_print_list pp_print_expr ",@ ") e2
        (pp_print_list pp_print_expr ",@ ") e3

    | Activate (p, i, c, r, l) ->

      Format.fprintf ppf
        "(activate (restart %a every %a) every %a) (%a)"
        pp_print_ident i
        pp_print_expr r
        pp_print_expr c
        (pp_print_list pp_print_expr ",@ ") l 
        
    | Merge (p, c, l) ->

      Format.fprintf ppf
        "merge(%a,@ %a)"
        pp_print_ident c
        (pp_print_list (fun fmt (c,e) ->
             Format.fprintf fmt "%a -> %a"
               pp_print_ident c
               pp_print_expr e) ",@ ") l 

    | RestartEvery (p, i, l, c) ->
      Format.fprintf ppf
        "(restart %a every %a)(%a)"
        pp_print_ident i
        pp_print_expr c
        (pp_print_list pp_print_expr ",@ ") l 

    | Pre (p, e) -> p1 p "pre" e
    | Last (p, id) ->
      Format.fprintf ppf "last %a%a" ppos p pp_print_ident id
    | Fby (p, e1, i, e2) -> 

      Format.fprintf ppf 
        "%afby(p, %a,@ %d,@ %a)" 
        ppos p 
        pp_print_expr e1 
        i 
        pp_print_expr e2

    | Arrow (p, e1, e2) -> p2 p "->" e1 e2

    | Call (p, id, l) ->

      Format.fprintf ppf 
        "%a%a(%a)" 
        ppos p
        pp_print_ident id
        (pp_print_list pp_print_expr ",@ ") l

    | CallParam (p, id, t, l) -> 

      Format.fprintf ppf 
        "%a%a<<%a>>(%a)" 
        ppos p
        pp_print_ident id
        (pp_print_list pp_print_lustre_type "@ ") t
        (pp_print_list pp_print_expr ",@ ") l
        

(* Pretty-print an array slice *)
and pp_print_array_slice ppf (l, u) =
  if l = u then
    Format.fprintf ppf "%a" pp_print_expr l
  else
    Format.fprintf ppf "%a..%a" pp_print_expr l pp_print_expr u

and pp_print_field_assign ppf (i, e) = 

  Format.fprintf ppf 
    "@[<hv 2>%a =@ %a@]"
    pp_print_index i
    pp_print_expr e


(* Pretty-print a Lustre type *)
and pp_print_lustre_type ppf = function

  | Bool pos -> Format.fprintf ppf "bool"

  | Int pos -> Format.fprintf ppf "int"

  | IntRange (pos, l, u) -> 

    Format.fprintf ppf 
      "subrange [%a,%a] of int" 
      pp_print_expr l
      pp_print_expr u

  | Real pos -> Format.fprintf ppf "real"

  | UserType (pos, s) -> 

    Format.fprintf ppf "%a" pp_print_ident s

  | TupleType (pos, l) -> 

    Format.fprintf ppf 
      "@[<hv 1>[%a]@]" 
      (pp_print_list pp_print_lustre_type ",@ ") l

  | RecordType (pos, l) -> 

    Format.fprintf ppf 
      "struct @[<hv 2>{ %a }@]" 
      (pp_print_list pp_print_typed_ident ";@ ") l

  | ArrayType (pos, (t, e)) -> 

    Format.fprintf ppf 
      "(%a^%a)" 
      pp_print_lustre_type t 
      pp_print_expr e

  | EnumType (pos, _, l) -> 

    Format.fprintf ppf 
      "enum @[<hv 2>{ %a }@]" 
      (pp_print_list Format.pp_print_string ",@ ") l


(* Pretty-print a typed identifier *)
and pp_print_typed_ident ppf (p, s, t) = 
  Format.fprintf ppf 
    "@[<hov 2>%s:@ %a@]" 
    s 
    pp_print_lustre_type t


(* Pretty-print a typed identifier *)
and pp_print_typed_decl ppf (p, s, t) = 
  Format.fprintf ppf 
    "@[<hov 2>%s:@ %a@]" 
    s 
    pp_print_lustre_type t


(* Pretty-print a typed identifier with a clock *)
and pp_print_clocked_typed_ident ppf (pos, s, t, c) = 
  Format.fprintf ppf 
    "@[<hov 2>%a:@ %a%a@]" 
    pp_print_ident s 
    pp_print_lustre_type t 
    pp_print_clock_expr c


(* Pretty-print a typed identifier with a clock, possibly constant *)
and pp_print_const_clocked_typed_ident ppf (pos, s, t, c, o) = 
  Format.fprintf ppf "@[<hov 2>%t%a:@ %a%a@]" 
    (function ppf -> if o then Format.fprintf ppf "const ")
    pp_print_ident s 
    pp_print_lustre_type t 
    pp_print_clock_expr c


and pp_print_label_or_index ppf = function 

  | Label (pos, i) -> pp_print_index ppf i
  | Index (pos, e) -> pp_print_expr ppf e

(* Pretty-print a type declaration *)
let pp_print_type_decl ppf = function

  | AliasType (pos, s, t) -> 
    
    Format.fprintf ppf 
      "@[<hv 2>%a =@ %a@]" 
      pp_print_ident s 
      pp_print_lustre_type t

  | FreeType (pos, t) -> 

    Format.fprintf ppf "%a" pp_print_ident t 


(* Pretty-print a variable declaration *)
let pp_print_var_decl ppf = function 

  | (pos, s, t, c) -> 

    Format.fprintf ppf 
      "@[<hov 2>%a:@ %a%a;@]" 
      pp_print_ident s 
      pp_print_lustre_type t
      pp_print_clock_expr c


(* Pretty-print a constant declaration *)
let pp_print_const_decl ppf = function

  | FreeConst (pos, s, t) -> 

    Format.fprintf ppf 
      "@[<hov 2>const %a:@ %a;@]" 
      pp_print_ident s 
      pp_print_lustre_type t

  | UntypedConst (pos, s, e) -> 

    Format.fprintf ppf 
      "@[<hov 2>const %a =@ %a;@]" 
      pp_print_ident s 
      pp_print_expr e

  | TypedConst (pos, s, e, t) -> 

    Format.fprintf ppf 
      "@[<hov 2>const %a:@ %a =@ %a;@]" 
      pp_print_ident s 
      pp_print_lustre_type t
      pp_print_expr e


(* Pretty-print a single static node parameter *)
let pp_print_node_param ppf = function

  | TypeParam t ->
    Format.fprintf ppf "type %a" pp_print_ident t


(* Pretty-print a list of static node parameters *)
let pp_print_node_param_list ppf = function

  | [] -> ()

  | l ->
    
    Format.fprintf ppf
      "@[<hv 2><<%a>>@]"
      (pp_print_list pp_print_node_param ";@ ") l


(* Pretty-print a node-local variable declaration, skip others *)
let pp_print_node_local_decl_var ppf = function

  | NodeVarDecl (pos, v) -> pp_print_var_decl ppf v

  | _ -> ()


(* Pretty-print a node-local constant declaration, skip others *)
let pp_print_node_local_decl_const ppf = function

  | NodeConstDecl (pos, c) -> pp_print_const_decl ppf c

  | _ -> ()


(* Pretty-print a node-local declaration *)
let pp_print_node_local_decl ppf l = 

  let c, v = 
    List.partition (function NodeConstDecl _ -> true | _ -> false) l 
  in

  if c = [] then () else 

    Format.fprintf ppf 
      "%a@ " 
      (pp_print_list pp_print_node_local_decl_const "@;<1 -2>") c;

  if v = [] then () else 

    Format.fprintf ppf
      "@[<hv 2>var@ %a@]@ "
      (pp_print_list pp_print_node_local_decl_var "@ ") v 


let pp_print_array_def_index ppf ident =

  Format.fprintf ppf
    "[%a]"
    pp_print_ident ident


let rec pp_print_struct_item ppf = function

  | SingleIdent (pos, s) -> Format.fprintf ppf "%a" pp_print_ident s

  | TupleStructItem (pos, l) -> 

    Format.fprintf ppf 
      "@[<hv 1>[%a]@]" 
      (pp_print_list pp_print_struct_item ",@ ") l

  | TupleSelection (pos, e, i) -> 

    Format.fprintf ppf
      "%a[%a]"
      pp_print_ident e
      pp_print_expr i

  | FieldSelection (pos, e, i) -> 

    Format.fprintf ppf
      "%a.%a"
      pp_print_ident e
      pp_print_ident i

  | ArraySliceStructItem (pos, e, i) -> 

    Format.fprintf ppf
      "%a@[<hv 1>[%a]@]" 
      pp_print_ident e
      (pp_print_list pp_print_array_slice ",@ ") i
                            
  | ArrayDef (pos, i, l) ->

    Format.fprintf ppf
      "%a%a"
      pp_print_ident i
      (pp_print_list pp_print_array_def_index "") l


let pp_print_eq_lhs ppf = function

  | StructDef (pos, [l]) ->
    pp_print_struct_item ppf l
      
  | StructDef (pos, l) ->
    Format.fprintf ppf "(%a)"
      (pp_print_list pp_print_struct_item ",") l
  

let rec pp_print_body ppf = function

  | Assert (pos, e) -> 

    Format.fprintf ppf "assert %a;" pp_print_expr e

  | Equation (pos, lhs, e) -> 
    
    Format.fprintf ppf 
      "@[<hv 2>%a =@ %a;@]" 
      pp_print_eq_lhs lhs
      pp_print_expr e

  | Automaton (_, name, states, returns) ->
    pp_print_automaton ppf name states returns


(* Pretty-print a node equation *)
and pp_print_node_item ppf = function
  
  | Body b -> pp_print_body ppf b

  | AnnotMain true -> Format.fprintf ppf "--%%MAIN;"

  | AnnotMain false -> Format.fprintf ppf "--!MAIN : false;"

  | AnnotProperty (pos, None, e) ->
    Format.fprintf ppf "--%%PROPERTY %a;" pp_print_expr e 

  | AnnotProperty (pos, Some name, e) ->
    Format.fprintf ppf "--%%PROPERTY \"%s\" %a;" name pp_print_expr e 


and pp_print_automaton ppf name states returns =
  Format.fprintf ppf "@[<hv 2>automaton %s@.%a@]returns %a;"
    (match name with Some n -> n | None -> "")
    pp_print_states states
    pp_print_auto_returns returns


and pp_print_auto_returns ppf = function
  | Given l -> pp_print_list pp_print_ident "," ppf l
  | Inferred -> Format.fprintf ppf ".."

and pp_print_states ppf =
  pp_print_list pp_print_state "@." ppf


and pp_print_state ppf =
  function State (_, name, init, locals, eqs, unless, until) ->
    Format.fprintf ppf "state %s@.@[<hv 2>%a%a@[<hv 2>let@.%a@]@.tel@]@.%a" name
      (pp_print_auto_trans "unless") unless
      pp_print_node_local_decl locals
      (pp_print_list pp_print_body "@ ") eqs
      (pp_print_auto_trans "until") until

and pp_print_auto_trans kind ppf = function
  | None -> ()
  | Some (_, br) ->
    Format.fprintf ppf "%s %a;@." kind pp_print_transition_branch br

and pp_print_transition_branch ppf = function
  | Target (TransRestart (_, (_, t))) -> Format.fprintf ppf "restart %s" t
  | Target (TransResume (_, (_, t))) -> Format.fprintf ppf "resume %s" t
  | TransIf (_, e, br, None) ->
    Format.fprintf ppf "if@ %a@ %a"
      pp_print_expr e
      pp_print_transition_branch br
  | TransIf (_, e, br, Some br2) ->
    Format.fprintf ppf "if@ %a@ %a@ else@ %a@ end"
      pp_print_expr e
      pp_print_transition_branch br
      pp_print_transition_branch br2


let pp_print_contract_ghost_const ppf = function 

  | FreeConst (pos, s, t) -> 

    Format.fprintf ppf 
      "@[<hv 3>const %a:@ %a;@]" 
      pp_print_ident s 
      pp_print_lustre_type t

  | UntypedConst (pos, s, e) -> 

    Format.fprintf ppf 
      "@[<hv 3>const %a =@ %a;@]" 
      pp_print_ident s 
      pp_print_expr e

  | TypedConst (pos, s, e, t) -> 

    Format.fprintf ppf 
      "@[<hv 3>const %a:@ %a =@ %a;@]" 
      pp_print_ident s 
      pp_print_lustre_type t
      pp_print_expr e

    
let pp_print_contract_ghost_var ppf = function 

  | FreeConst (pos, s, t) -> 

    Format.fprintf ppf 
      "@[<hv 3>var %a:@ %a;@]" 
      pp_print_ident s 
      pp_print_lustre_type t

  | UntypedConst (pos, s, e) -> 

    Format.fprintf ppf 
      "@[<hv 3>var %a =@ %a;@]" 
      pp_print_ident s 
      pp_print_expr e

  | TypedConst (pos, s, e, t) -> 

    Format.fprintf ppf 
      "@[<hv 3>var %a:@ %a =@ %a;@]" 
      pp_print_ident s 
      pp_print_lustre_type t
      pp_print_expr e

    
let pp_print_contract_assume ppf (_, n, e) =
  Format.fprintf
    ppf
    "@[<hv 3>assume%s@ %a;@]"
    (match n with None -> "" | Some s -> " \""^s^"\"")
    pp_print_expr e

let pp_print_contract_guarantee ppf (_, n, e) =
  Format.fprintf
    ppf
    "@[<hv 3>guarantee%s@ %a;@]"
    (match n with None -> "" | Some s -> " \""^s^"\"")
    pp_print_expr e

    
let pp_print_contract_require ppf (_, n, e) =
  Format.fprintf
    ppf
    "@[<hv 3>require%s@ %a;@]"
    (match n with None -> "" | Some s -> " \""^s^"\"")
    pp_print_expr e

let pp_print_contract_ensure ppf (_, n, e) =
  Format.fprintf
    ppf
    "@[<hv 3>ensure%s@ %a;@]"
    (match n with None -> "" | Some s -> " \""^s^"\"")
    pp_print_expr e

let cond_new_line b fmt () =
  if b then Format.fprintf fmt "@ " else Format.fprintf fmt ""

let pp_print_contract_mode ppf (_, id, reqs, enss) =
  Format.fprintf
    ppf
    "@[<hv 2>mode %a (%a%a%a%a@]%a) ;"
    pp_print_ident id
    (cond_new_line (reqs <> [])) ()
    (pp_print_list pp_print_contract_require "@ ") reqs
    (cond_new_line (enss <> [])) ()
    (pp_print_list pp_print_contract_ensure "@ ") enss
    (cond_new_line ((reqs,enss) <> ([],[]))) ()

let pp_print_contract_call fmt (_, id, in_params, out_params) =
  Format.fprintf
    fmt "@[<hov 2>import %a (@,%a@,) (@,%a@,) ;@]"
    pp_print_ident id
    (pp_print_list pp_print_expr ", ") in_params
    (pp_print_list pp_print_expr ", ") out_params

let all_empty = List.for_all (fun l -> l = [])

let pp_print_contract_item fmt = function
  | GhostConst c -> pp_print_contract_ghost_const fmt c
  | GhostVar v -> pp_print_contract_ghost_var fmt v
  | Assume a -> pp_print_contract_assume fmt a
  | Guarantee g -> pp_print_contract_guarantee fmt g
  | Mode m -> pp_print_contract_mode fmt m
  | ContractCall call -> pp_print_contract_call fmt call


let pp_print_contract fmt contract =
  Format.fprintf fmt "@[<v>%a@]"
    (pp_print_list pp_print_contract_item "@ ") contract


let pp_print_contract_spec ppf = function
| None -> ()
| Some contract ->
  Format.fprintf 
    ppf
    "@[<v 2>(*@contract@ %a@]@ *)@ "
    pp_print_contract contract


(* Pretty-prints a contract node. *)
let pp_print_contract_node ppf (
  id, _, i, o, contract
) =
  Format.fprintf ppf "@[<v>\
      contract %s (@   \
        @[<v>%a@]@ \
      ) returns (@   \
        @[<v>%a@]@ \
      ) ;@ \
      spec@   \
        %a@ \
      ceps\
      @]
    @]"
    id
    (pp_print_list pp_print_const_clocked_typed_ident ";@ ") i
    (pp_print_list pp_print_clocked_typed_ident ";@ ") o
    pp_print_contract contract 


let pp_print_node_or_fun_decl is_fun ppf (
  pos, (n, ext, p, i, o, l, e, r)
) =

    Format.fprintf ppf
      "@[<hv>@[<hv 2>%s%s %a%t@ \
       @[<hv 1>(%a)@]@;<1 -2>\
       returns@ @[<hv 1>(%a)@];@]@ \
       %a@ \
       %a@ \
       @[<v 2>let@ \
       %a@;<1 -2>\
       tel;@]@]"
      (if ext then "extern " else "")
      (if is_fun then "function" else "node")
      pp_print_ident n 
      (function ppf -> pp_print_node_param_list ppf p)
      (pp_print_list pp_print_const_clocked_typed_ident ";@ ") i
      (pp_print_list pp_print_clocked_typed_ident ";@ ") o
      pp_print_contract_spec
      r
      pp_print_node_local_decl l
      (pp_print_list pp_print_node_item "@ ") e


(* Pretty-print a declaration *)
let pp_print_declaration ppf = function

  | TypeDecl (pos, t) -> 

    Format.fprintf ppf "type %a;" pp_print_type_decl t

  | ConstDecl (pos, c) -> pp_print_const_decl ppf c

  | NodeDecl (pos, decl) ->
    pp_print_node_or_fun_decl false ppf (pos, decl)

  | FuncDecl (pos, decl) ->
    pp_print_node_or_fun_decl true ppf (pos, decl)

  | ContractNodeDecl (pos, (n,p,i,o,e)) ->

     Format.fprintf
       ppf
       "@[<hv>@[<hv 2>contract %a%t@ \
        @[<hv 1>(%a)@]@;<1 -2>\
        returns@ @[<hv 1>(%a)@];@]@ \
        @[<hv 2>let@ \
        %a@;<1 -2>\
        tel;@]@]"
       pp_print_ident n
       (function ppf -> pp_print_node_param_list ppf p)
       (pp_print_list pp_print_const_clocked_typed_ident ";@ ") i
       (pp_print_list pp_print_clocked_typed_ident ";@ ") o
       pp_print_contract e

  | NodeParamInst (pos, (n, s, p)) -> 

    Format.fprintf ppf
      "@[<hv>@[<hv 2>node %a =@ %a@[<hv 2><<%a>>@];@]" 
      pp_print_ident n 
      pp_print_ident n 
      (pp_print_list pp_print_lustre_type "@ ") p


let pp_print_program ppf p =

  Format.fprintf ppf
    "@[<v>%a@]" 
    (pp_print_list pp_print_declaration "@ ") 
    p




(***********)
(* Helpers *)
(***********)

let pos_of_expr = function
  | Ident (pos , _) | ModeRef (pos , _ ) | RecordProject (pos , _ , _)
  | TupleProject (pos , _ , _) | StructUpdate (pos , _ , _ , _) | True pos
  | False pos | Num (pos , _) | Dec (pos , _) | ToInt (pos , _)
  | ToReal (pos , _) | ExprList (pos , _ ) | TupleExpr (pos , _ )
  | ArrayExpr (pos , _ ) | ArrayConstr (pos , _ , _ )
  | ArraySlice (pos , _ , _) | ArrayConcat (pos , _ , _)
  | RecordExpr (pos , _ , _) | Not (pos , _) | And (pos , _ , _)
  | Or (pos , _ , _) | Xor (pos , _ , _) | Impl (pos , _ , _)
  | OneHot (pos , _ ) | Uminus (pos , _) | Mod (pos , _ , _)
  | Minus (pos , _ , _) | Plus (pos , _ , _) | Div (pos , _ , _)
  | Times (pos , _ , _) | IntDiv (pos , _ , _) | Ite (pos , _ , _ , _)
  | With (pos , _ , _ , _) | Eq (pos , _ , _) | Neq (pos , _ , _)
  | Lte (pos , _ , _) | Lt (pos , _ , _) | Gte (pos , _ , _) | Gt (pos , _ , _)
  | Forall (pos, _, _) | Exists (pos, _, _)
  | When (pos , _ , _) | Current (pos , _) | Condact (pos , _ , _ , _ , _, _)
  | Activate (pos , _ , _ , _ , _) | Merge (pos , _ , _ ) | Pre (pos , _)
  | Last (pos , _) | RestartEvery (pos, _, _, _)
  | Fby (pos , _ , _ , _) | Arrow (pos , _ , _) | Call (pos , _ , _ )
  | CallParam (pos , _ , _ , _ )
    -> pos


let rec has_unguarded_pre ung = function
  | True _ | False _ | Num _ | Dec _ | Ident _ | ModeRef _ -> false
    
  | RecordProject (_, e, _) | ToInt (_, e) | ToReal (_, e)
  | Not (_, e) | Uminus (_, e) | Current (_, e) | When (_, e, _)
  | Forall (_, _, e) | Exists (_, _, e) -> has_unguarded_pre ung e

  | TupleProject (_, e1, e2) | And (_, e1, e2) | Or (_, e1, e2)
  | Xor (_, e1, e2) | Impl (_, e1, e2) | ArrayConstr (_, e1, e2) 
  | Mod (_, e1, e2) | Minus (_, e1, e2) | Plus (_, e1, e2) | Div (_, e1, e2)
  | Times (_, e1, e2) | IntDiv (_, e1, e2) | Eq (_, e1, e2) | Neq (_, e1, e2)
  | Lte (_, e1, e2) | Lt (_, e1, e2) | Gte (_, e1, e2) | Gt (_, e1, e2)
  | ArrayConcat (_, e1, e2) ->
    let u1 = has_unguarded_pre ung e1 in
    let u2 = has_unguarded_pre ung e2 in

    u1 || u2

  | Ite (_, e1, e2, e3) | With (_, e1, e2, e3)
  | ArraySlice (_, e1, (e2, e3)) ->
    let u1 = has_unguarded_pre ung e1 in
    let u2 = has_unguarded_pre ung e2 in
    let u3 = has_unguarded_pre ung e3 in
    u1 || u2 || u3
  
  | ExprList (_, l) | TupleExpr (_, l) | ArrayExpr (_, l)
  | OneHot (_, l) | Call (_, _, l) | CallParam (_, _, _, l) ->
    let us = List.map (has_unguarded_pre ung) l in
    List.exists KindLib.identity us

  | Merge (_, _, l) ->
    let us = List.map (has_unguarded_pre ung) (List.map snd l) in
    List.exists KindLib.identity us

  | RestartEvery (_, _, l, e) ->
    let us = List.map (has_unguarded_pre ung) (e :: l) in
    List.exists KindLib.identity us

  | Activate (_, _, e, r, l)  ->
    let us = List.map (has_unguarded_pre ung) (e :: r :: l) in
    List.exists KindLib.identity us

  | Condact (_, e, r, _, l1, l2) ->
    let us = List.map (has_unguarded_pre ung) (e :: r :: l1 @ l2) in
    List.exists KindLib.identity us

  | RecordExpr (_, _, ie) ->
    let us = List.map (fun (_, e) -> has_unguarded_pre ung e) ie in
    List.exists KindLib.identity us

  | StructUpdate (_, e1, li, e2) ->
    let u1 = has_unguarded_pre ung e1 in
    let us = List.map (function
        | Label _ -> false
        | Index (_, e) -> has_unguarded_pre ung e
      ) li in
    let u2 = has_unguarded_pre ung e2 in
    u1 || u2 || List.exists KindLib.identity us

  | Fby (_, e1, _, e2) ->
    let u1, u2 = has_unguarded_pre ung e1, has_unguarded_pre ung e2 in
    u1 || u2

  | Pre (pos, e) as p ->
    if ung then begin
      (* Fail only if in strict mode *)
      let err_or_warn = warn_at_position in

      err_or_warn pos
        (Format.asprintf "@[<hov 2>Unguarded pre in expression@ %a@]"
           pp_print_expr p)
    end;

    let u = has_unguarded_pre true e in
    ung || u

  | Last _ -> false

  (* TODO: Only report unguarded lasts contained in automaton states
     that are activable at the initial state *)
(*
  | Last (pos, _) as p ->
    if ung then begin
      (* Fail only if in strict mode *)
      let err_or_warn =
        if Flags.lus_strict () then error_at_position else warn_at_position in

      err_or_warn pos
        (Format.asprintf "@[<hov 2>Unguarded pre in expression@ %a@]"
           pp_print_expr p)
    end;
    ung
*)
    
  | Arrow (_, e1, e2) ->
    let u1 = has_unguarded_pre ung e1 in
    let u2 = has_unguarded_pre false e1 in
    u1 || u2

let has_unguarded_pre e =
  let u = has_unguarded_pre true e in
  u

(** If second argument is `Some _`, returns that. Otherwise runs `f`. *)
let unwrap_or f = function
| None -> f ()
| res -> res

(** If input list contains `Some _`, returns that. Otherwise returns `None`. *)
let some_of_list = List.fold_left (
  function
  | None -> KindLib.identity
  | res -> (fun _ -> res)
) None

(** Checks whether an expression has a `pre` or a `->`. *)
let rec has_pre_or_arrow = function
  | True _ | False _ | Num _ | Dec _ | Ident _ | ModeRef _ -> None
    
  | RecordProject (_, e, _) | ToInt (_, e) | ToReal (_, e)
  | Not (_, e) | Uminus (_, e) | Current (_, e) | When (_, e, _)
  | Forall (_, _, e) | Exists (_, _, e) ->
    has_pre_or_arrow e

  | TupleProject (_, e1, e2) | And (_, e1, e2) | Or (_, e1, e2)
  | Xor (_, e1, e2) | Impl (_, e1, e2) | ArrayConstr (_, e1, e2) 
  | Mod (_, e1, e2) | Minus (_, e1, e2) | Plus (_, e1, e2) | Div (_, e1, e2)
  | Times (_, e1, e2) | IntDiv (_, e1, e2) | Eq (_, e1, e2) | Neq (_, e1, e2)
  | Lte (_, e1, e2) | Lt (_, e1, e2) | Gte (_, e1, e2) | Gt (_, e1, e2)
  | ArrayConcat (_, e1, e2) -> (
    match has_pre_or_arrow e1 with
    | None -> has_pre_or_arrow e2
    | res -> res
  )

  | Ite (_, e1, e2, e3) | With (_, e1, e2, e3)
  | ArraySlice (_, e1, (e2, e3)) ->
    has_pre_or_arrow e1
    |> unwrap_or (
      fun _ ->
        has_pre_or_arrow e2
        |> unwrap_or (
          fun _ -> has_pre_or_arrow e3
        )
    )
  
  | ExprList (_, l) | TupleExpr (_, l) | ArrayExpr (_, l)
  | OneHot (_, l) | Call (_, _, l) | CallParam (_, _, _, l) ->
    List.map has_pre_or_arrow l
    |> some_of_list

  | Merge (_, _, l) ->
    List.map has_pre_or_arrow (List.map snd l)
    |> some_of_list

  | RestartEvery (_, _, l, e) ->
    List.map has_pre_or_arrow (e :: l)
    |> some_of_list

  | Activate (_, _, e, r, l) ->
    List.map has_pre_or_arrow (e :: r :: l)
    |> some_of_list

  | Condact (_, e, r, _, l1, l2) ->
    List.map has_pre_or_arrow (e :: r :: l1 @ l2)
    |> some_of_list

  | RecordExpr (_, _, ie) ->
    List.map (fun (_, e) -> has_pre_or_arrow e) ie
    |> some_of_list

  | StructUpdate (_, e1, li, e2) ->
    has_pre_or_arrow e1
    |> unwrap_or (
      fun _ ->
        has_pre_or_arrow e2
        |> unwrap_or (
          fun _ ->
            List.map (function
              | Label _ -> None
              | Index (_, e) -> has_pre_or_arrow e
            ) li
            |> some_of_list
        )
    )

  | Fby (_, e1, _, e2) ->
    has_pre_or_arrow e1
    |> unwrap_or (fun _ -> has_pre_or_arrow e2)

  | Pre (pos, _) | Last (pos, _) -> Some pos

  | Arrow (pos, e1, e2) -> Some pos


(** Returns identifiers under a last operator *)
let rec lasts_of_expr acc = function
  | True _ | False _ | Num _ | Dec _ | Ident _ | ModeRef _ -> acc
    
  | RecordProject (_, e, _) | ToInt (_, e) | ToReal (_, e)
  | Not (_, e) | Uminus (_, e) | Current (_, e) | When (_, e, _)
  | Forall (_, _, e) | Exists (_, _, e) ->
    lasts_of_expr acc e

  | TupleProject (_, e1, e2) | And (_, e1, e2) | Or (_, e1, e2)
  | Xor (_, e1, e2) | Impl (_, e1, e2) | ArrayConstr (_, e1, e2) 
  | Mod (_, e1, e2) | Minus (_, e1, e2) | Plus (_, e1, e2) | Div (_, e1, e2)
  | Times (_, e1, e2) | IntDiv (_, e1, e2) | Eq (_, e1, e2) | Neq (_, e1, e2)
  | Lte (_, e1, e2) | Lt (_, e1, e2) | Gte (_, e1, e2) | Gt (_, e1, e2)
  | ArrayConcat (_, e1, e2) ->
    lasts_of_expr (lasts_of_expr acc e1) e2

  | Ite (_, e1, e2, e3) | With (_, e1, e2, e3)
  | ArraySlice (_, e1, (e2, e3)) ->
    lasts_of_expr (lasts_of_expr (lasts_of_expr acc e1) e2) e3
  
  | ExprList (_, l) | TupleExpr (_, l) | ArrayExpr (_, l)
  | OneHot (_, l) | Call (_, _, l) | CallParam (_, _, _, l) ->
    List.fold_left lasts_of_expr acc l

  | Merge (_, _, l) ->
    List.fold_left (fun acc (_, e) -> lasts_of_expr acc e) acc l

  | RestartEvery (_, _, l, e) ->
    List.fold_left lasts_of_expr acc (e :: l)

  | Activate (_, _, e, r, l) ->
    List.fold_left lasts_of_expr acc (e :: r :: l)

  | Condact (_, e, r, _, l1, l2) ->
    List.fold_left lasts_of_expr acc (e :: r :: l1 @ l2)

  | RecordExpr (_, _, ie) ->
    List.fold_left (fun acc (_, e) -> lasts_of_expr acc e) acc ie

  | StructUpdate (_, e1, li, e2) ->
    let acc = lasts_of_expr (lasts_of_expr acc e1) e2 in
    List.fold_left (fun acc -> function
        | Label _ -> acc
        | Index (_, e) -> lasts_of_expr acc e
      ) acc li
    
  | Fby (_, e1, _, e2) ->
    lasts_of_expr (lasts_of_expr acc e1) e2

  | Pre (pos, e) -> lasts_of_expr acc e
                      
  | Last (pos, i) -> SI.add i acc

  | Arrow (pos, e1, e2) ->
    lasts_of_expr (lasts_of_expr acc e1) e2


let rec replace_lasts allowed prefix acc ee = match ee with
  | True _ | False _ | Num _ | Dec _ | Ident _ | ModeRef _ ->
    ee, acc
    
  | RecordProject (pos, e, i) ->
    let e', acc' = replace_lasts allowed prefix acc e in
    if e == e' then ee, acc
    else RecordProject (pos, e', i), acc'
         
  | ToInt (pos, e) ->
    let e', acc' = replace_lasts allowed prefix acc e in
    if e == e' then ee, acc
    else ToInt (pos, e'), acc'
                      
  | ToReal (pos, e) ->
    let e', acc' = replace_lasts allowed prefix acc e in
    if e == e' then ee, acc
    else ToReal (pos, e'), acc'

  | Not (pos, e) ->
    let e', acc' = replace_lasts allowed prefix acc e in
    if e == e' then ee, acc
    else Not (pos, e'), acc'

  | Uminus (pos, e) ->
    let e', acc' = replace_lasts allowed prefix acc e in
    if e == e' then ee, acc
    else Uminus (pos, e'), acc'

  | Current (pos, e) ->
    let e', acc' = replace_lasts allowed prefix acc e in
    if e == e' then ee, acc
    else Current (pos, e'), acc'

  | When (pos, e, c) ->
    let e', acc' = replace_lasts allowed prefix acc e in
    if e == e' then ee, acc
    else When (pos, e', c), acc'

  | Forall (pos, vs, e) ->
    let e', acc' = replace_lasts allowed prefix acc e in
    if e == e' then ee, acc
    else Forall (pos, vs, e'), acc'

  | Exists (pos, vs, e) ->
    let e', acc' = replace_lasts allowed prefix acc e in
    if e == e' then ee, acc
    else Exists (pos, vs, e'), acc'

  | TupleProject (pos, e1, e2)
  | And (pos, e1, e2) | Or (pos, e1, e2) | Xor (pos, e1, e2)
  | Impl (pos, e1, e2) | ArrayConstr (pos, e1, e2) | Mod (pos, e1, e2)
  | Minus (pos, e1, e2) | Plus (pos, e1, e2) | Div (pos, e1, e2)
  | Times (pos, e1, e2) | IntDiv (pos, e1, e2) | Eq (pos, e1, e2)
  | Neq (pos, e1, e2) | Lte (pos, e1, e2) | Lt (pos, e1, e2)
  | Gte (pos, e1, e2) | Gt (pos, e1, e2) | ArrayConcat (pos, e1, e2) ->
    let e1', acc' = replace_lasts allowed prefix acc e1 in
    let e2', acc' = replace_lasts allowed prefix acc' e2 in
    if e1 == e1' && e2 == e2' then ee, acc
    else (match ee with
        | TupleProject (pos, e1, e2) -> TupleProject (pos, e1', e2')
        | And (pos, e1, e2) -> And (pos, e1', e2')
        | Or (pos, e1, e2) -> Or (pos, e1', e2')
        | Xor (pos, e1, e2) -> Xor (pos, e1', e2')
        | Impl (pos, e1, e2) -> Impl (pos, e1', e2')
        | ArrayConstr (pos, e1, e2)  -> ArrayConstr (pos, e1', e2') 
        | Mod (pos, e1, e2) -> Mod (pos, e1', e2')
        | Minus (pos, e1, e2) -> Minus (pos, e1', e2')
        | Plus (pos, e1, e2) -> Plus (pos, e1', e2')
        | Div (pos, e1, e2) -> Div (pos, e1', e2')
        | Times (pos, e1, e2) -> Times (pos, e1', e2')
        | IntDiv (pos, e1, e2) -> IntDiv (pos, e1', e2')
        | Eq (pos, e1, e2) -> Eq (pos, e1', e2')
        | Neq (pos, e1, e2) -> Neq (pos, e1', e2')
        | Lte (pos, e1, e2) -> Lte (pos, e1', e2')
        | Lt (pos, e1, e2) -> Lt (pos, e1', e2')
        | Gte (pos, e1, e2) -> Gte (pos, e1', e2')
        | Gt (pos, e1, e2) -> Gt (pos, e1', e2')
        | ArrayConcat (pos, e1, e2) -> ArrayConcat (pos, e1', e2')
        | _ -> assert false
      ), acc'

  | Ite (_, e1, e2, e3) | With (_, e1, e2, e3)
  | ArraySlice (_, e1, (e2, e3)) ->
    let e1', acc' = replace_lasts allowed prefix acc e1 in
    let e2', acc' = replace_lasts allowed prefix acc' e2 in
    let e3', acc' = replace_lasts allowed prefix acc' e3 in
    if e1 == e1' && e2 == e2' && e3 == e3' then ee, acc
    else (match ee with
        | Ite (pos, e1, e2, e3) -> Ite (pos, e1', e2', e3')
        | With (pos, e1, e2, e3) -> With (pos, e1', e2', e3')
        | ArraySlice (pos, e1, (e2, e3)) -> ArraySlice (pos, e1', (e2', e3'))
        | _ -> assert false
      ), acc'
  
  | ExprList (_, l) | TupleExpr (_, l) | ArrayExpr (_, l)
  | OneHot (_, l) | Call (_, _, l) | CallParam (_, _, _, l) ->
    let l', acc' =
      List.fold_left (fun (l, acc) e ->
          let e, acc = replace_lasts allowed prefix acc e in
          e :: l, acc
        ) ([], acc) l in
    let l' = List.rev l' in
    if try List.for_all2 (==) l l' with _ -> false then ee, acc
    else (match ee with
        | ExprList (pos, l) -> ExprList (pos, l')
        | TupleExpr (pos, l) -> TupleExpr (pos, l')
        | ArrayExpr (pos, l) -> ArrayExpr (pos, l')
        | OneHot (pos, l) -> OneHot (pos, l')
        | Call (pos, n, l) -> Call (pos, n, l')
        | CallParam (pos, n, t, l) -> CallParam (pos, n, t, l')
        | _ -> assert false
      ), acc'
      

  | Merge (pos, c, l) ->
    let l', acc' =
      List.fold_left (fun (l, acc) (c, e) ->
          let e, acc = replace_lasts allowed prefix acc e in
          (c, e) :: l, acc
        ) ([], acc) l in
    let l' = List.rev l' in
    if try List.for_all2 (fun (_, x) (_, x') -> x == x') l l' with _ -> false
    then ee, acc
    else Merge (pos, c, l'), acc'

  | RestartEvery (pos, n, l, e) ->
    let l', acc' =
      List.fold_left (fun (l, acc) e ->
          let e, acc = replace_lasts allowed prefix acc e in
          e :: l, acc
        ) ([], acc) l in
    let l' = List.rev l' in
    let e', acc' = replace_lasts allowed prefix acc' e in
    if try e == e' && List.for_all2 (==) l l'  with _ -> false then ee, acc
    else RestartEvery (pos, n, l', e'), acc

  | Activate (pos, n, e, r, l) ->
    let l', acc' =
      List.fold_left (fun (l, acc) e ->
          let e, acc = replace_lasts allowed prefix acc e in
          e :: l, acc
        ) ([], acc) l in
    let l' = List.rev l' in
    let e', acc' = replace_lasts allowed prefix acc' e in
    let r', acc' = replace_lasts allowed prefix acc' r in
    if try e == e' && r == r' &&
           List.for_all2 (==) l l'  with _ -> false then ee, acc
    else Activate (pos, n, e', r', l'), acc'

  | Condact (pos, e, r, n, l1, l2) ->
    let l1', acc' =
      List.fold_left (fun (l, acc) e ->
          let e, acc = replace_lasts allowed prefix acc e in
          e :: l, acc
        ) ([], acc) l1 in
    let l1' = List.rev l1 in
    let l2', acc' =
      List.fold_left (fun (l, acc) e ->
          let e, acc = replace_lasts allowed prefix acc e in
          e :: l, acc
        ) ([], acc') l2 in
    let l2' = List.rev l2 in
    let e', acc' = replace_lasts allowed prefix acc' e in
    let r', acc' = replace_lasts allowed prefix acc' r in
    if try e == e' && r == r' &&
           List.for_all2 (==) l1 l1' &&
           List.for_all2 (==) l2 l2'
      with _ -> false then ee, acc
    else Condact (pos, e', r', n, l1', l2'), acc'

  | RecordExpr (pos, n, ie) ->
    let ie', acc' =
      List.fold_left (fun (ie, acc) (i, e) ->
          let e, acc = replace_lasts allowed prefix acc e in
          (i, e) :: ie, acc
        ) ([], acc) ie in
    let ie' = List.rev ie' in
    if try List.for_all2 (fun (_, e) (_, e') -> e == e') ie ie' with _ -> false
    then ee, acc
    else RecordExpr (pos, n, ie'), acc'

  | StructUpdate (pos, e1, li, e2) ->
    let li', acc' =
      List.fold_left (fun (li, acc) -> function
          | Label _ as s -> s :: li, acc
          | Index (i, e) as s ->
            let e', acc' = replace_lasts allowed prefix acc e in
            if e == e' then s :: li, acc
            else Index (i, e') :: li, acc
        ) ([], acc) li in
    let li' = List.rev li' in
    let e1', acc' = replace_lasts allowed prefix acc' e1 in
    let e2', acc' = replace_lasts allowed prefix acc' e2 in
    if try e1 == e1' && e2 == e2' &&
           List.for_all2 (fun ei ei' -> match ei, ei' with
               | Label _, Label _ -> true
               | Index (_, e), Index (_, e') -> e == e'
               | _ -> false
             ) li li'
      with _ -> false then ee, acc
    else StructUpdate (pos, e1', li', e2'), acc'
        
  | Fby (pos, e1, i, e2) ->
    let e1', acc' = replace_lasts allowed prefix acc e1 in
    let e2', acc' = replace_lasts allowed prefix acc' e2 in
    if e1 == e1' && e2 == e2' then ee, acc
    else Fby (pos, e1', i, e2'), acc'
    
  | Pre (pos, e) ->
    let e', acc' = replace_lasts allowed prefix acc e in
    if e == e' then ee, acc else Pre (pos, e'), acc'
                      
  | Last (pos, i) ->
    if not (List.mem i allowed) then
      error_at_position pos
        "Only visible variables in the node are allowed under last";
    let acc = SI.add i acc in
    Ident (pos, prefix ^ ".last." ^ i), acc

  | Arrow (pos, e1, e2) ->
    let e1', acc' = replace_lasts allowed prefix acc e1 in
    let e2', acc' = replace_lasts allowed prefix acc' e2 in
    if e1 == e1' && e2 == e2' then ee, acc
    else Arrow (pos, e1', e2'), acc'



(** Checks whether a struct item has a `pre` or a `->`. *)
let rec struct_item_has_pre_or_arrow = function
| SingleIdent _ | FieldSelection _ | ArrayDef _ -> None
| TupleStructItem (_, l) ->
  List.map struct_item_has_pre_or_arrow l
  |> some_of_list
| ArraySliceStructItem (_, _, l) ->
  List.map (
    fun (e1, e2) ->
      has_pre_or_arrow e1
      |> unwrap_or (fun _ -> has_pre_or_arrow e2)
  ) l
  |> some_of_list
| TupleSelection (_, _, e) -> has_pre_or_arrow e


(** Checks whether a constant declaration has a `pre` or a `->`. *)
let const_decl_has_pre_or_arrow = function
| FreeConst _ -> None
| UntypedConst (_, _, e) -> has_pre_or_arrow e
| TypedConst (_, _, e, _) -> has_pre_or_arrow e



(** Checks whether a node local declaration has a `pre` or a `->`. *)
let node_local_decl_has_pre_or_arrow = function
| NodeConstDecl (_, decl) -> const_decl_has_pre_or_arrow decl
| NodeVarDecl _ -> None


(** Checks whether an equation lhs has a `pre` or a `->`. *)
let eq_lhs_has_pre_or_arrow = function
| StructDef (_, l) ->
  List.map struct_item_has_pre_or_arrow l
  |> some_of_list

(** Checks whether a node equation has a `pre` or a `->`. *)
let node_item_has_pre_or_arrow = function
| Body (Assert (_, e)) -> has_pre_or_arrow e
| Body (Equation (_, lhs, e)) ->
  eq_lhs_has_pre_or_arrow lhs
  |> unwrap_or (fun _ -> has_pre_or_arrow e)
| AnnotMain _ -> None
| AnnotProperty (_, _, e) -> has_pre_or_arrow e
| Body (Automaton _) -> assert false

(** Checks whether a contract node equation has a `pre` or a `->`.

Does not (cannot) check contract calls recursively, checks only inputs and
outputs. *)
let contract_node_equation_has_pre_or_arrow = function
| GhostConst decl
| GhostVar decl -> const_decl_has_pre_or_arrow decl
| Assume (_, _, e)
| Guarantee (_, _, e) -> has_pre_or_arrow e
| Mode (_, _, reqs, enss) ->
  List.map (fun (_, _, e) -> has_pre_or_arrow e) reqs
  |> some_of_list
  |> unwrap_or (
    fun _ ->
      List.map (fun (_, _, e) -> has_pre_or_arrow e) enss
      |> some_of_list
  )
| ContractCall (_, _, ins, outs) ->
  List.map has_pre_or_arrow ins
  |> some_of_list
  |> unwrap_or (
    fun _ ->
      List.map has_pre_or_arrow outs
      |> some_of_list
  )

(** Checks whether a contract has a `pre` or a `->`.

Does not (cannot) check contract calls recursively, checks only inputs and
outputs. *)
let contract_has_pre_or_arrow l =
  List.map contract_node_equation_has_pre_or_arrow l
  |> some_of_list


(* 
   Local Variables:
   compile-command: "make -k -C .."
   indent-tabs-mode: nil
   End: 
*)

