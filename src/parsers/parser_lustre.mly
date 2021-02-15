/********************************************************************/
/*                                                                  */
/*  The LustreC compiler toolset   /  The LustreC Development Team  */
/*  Copyright 2012 -    --   ONERA - CNRS - INPT                    */
/*                                                                  */
/*  LustreC is free software, distributed WITHOUT ANY WARRANTY      */
/*  under the terms of the GNU Lesser General Public License        */
/*  version 2.1.                                                    */
/*                                                                  */
/********************************************************************/

%{
open Utils
open Lustre_types
open Corelang
open Dimension

   
let get_loc () = Location.symbol_rloc ()

let mkident x = x, get_loc ()
let mktyp x = mktyp (get_loc ()) x
let mkotyp x = match x with Some t -> Some (mktyp t) | None -> None
let mkclock x = mkclock (get_loc ()) x
let mkvar_decl x loc = mkvar_decl loc ~orig:true x
let mkexpr x = mkexpr (get_loc ()) x
let mkeexpr x = mkeexpr (get_loc ()) x
let mkeq x = mkeq (get_loc ()) x
let mkassert x = mkassert (get_loc ()) x
let mktop_decl x = mktop_decl (get_loc ()) (Location.get_module ()) x
let mkpredef_call x = mkpredef_call (get_loc ()) x
let mkpredef_call_b f x1 x2 = mkpredef_call f [x1; x2]
let mkpredef_call_u f x = mkpredef_call f [x]

let mkdim_int x = mkdim_int (get_loc ()) x
(* let mkdim_bool b = mkdim_bool (get_loc ()) b *)
let mkdim_ident x = mkdim_ident (get_loc ()) x
let mkdim_appl x = mkdim_appl (get_loc ()) x
let mkdim_appl_b f x1 x2 = mkdim_appl f [x1; x2]
let mkdim_appl_u f x = mkdim_appl f [x]
let mkdim_ite x = mkdim_ite (get_loc ()) x

let mkarraytype = List.fold_left (fun t d -> Tydec_array (d, t))

let mkvdecls const typ clock expr =
  List.map (fun (id, loc) ->
      mkvar_decl (id,
                  mktyp (match typ with Some t -> t | None -> Tydec_any),
                  (match clock with Some ck -> ck | None -> mkclock Ckdec_any),
                  const, expr, None) loc)

(* let mkannots annots = { annots = annots; annot_loc = get_loc () } *)

let node_stack : ident list ref = ref []
(* let debug_calls () = Format.eprintf "call stack: %a@.@?" (Utils.fprintf_list ~sep:", " Format.pp_print_string) !node_stack *)
let push_node nd = node_stack := nd :: !node_stack; nd
let pop_node () = try node_stack := List.tl !node_stack with _ -> assert false
let get_current_node () = try List.hd !node_stack with _ -> assert false

let rec fby expr n init =
  if n <= 1 then
    mkexpr (Expr_arrow (init, mkexpr (Expr_pre expr)))
  else
    mkexpr (Expr_arrow (init, mkexpr (Expr_pre (fby expr (n - 1) init))))

 
%}

%token <int> INT
%token <Real.t> REAL

%token <string> STRING
%token AUTOMATON STATE UNTIL UNLESS RESTART RESUME 
%token ASSERT OPEN INCLUDE QUOTE POINT FUNCTION
%token <string> IDENT
%token <string> UIDENT
%token TRUE FALSE
%token <Lustre_types.expr_annot> ANNOT
%token <Lustre_types.spec_types> NODESPEC
%token LBRACKET RBRACKET LCUR RCUR LPAR RPAR SCOL COL COMMA COLCOL 
%token AMPERAMPER BARBAR NOT POWER
%token IF THEN ELSE
%token MERGE FBY WHEN WHENNOT EVERY
%token NODE LET TEL RETURNS VAR TYPE CONST
%token STRUCT ENUM
%token TINT TREAL TBOOL TCLOCK
%token EQ LT GT LTE GTE NEQ
%token AND OR XOR IMPL
%token MULT DIV MOD
%token MINUS PLUS 
%token PRE ARROW
%token REQUIRE ENSURE ASSUME GUARANTEES IMPORT CONTRACT
%token INVARIANT MODE CCODE MATLAB
%token EXISTS FORALL
%token PROTOTYPE LIB
%token EOF

%nonassoc p_string
(* %nonassoc p_vdecl *)
(* %left SCOL *)
%nonassoc EVERY
%nonassoc ELSE
%right ARROW FBY
%left WHEN WHENNOT 
%right IMPL
%left OR XOR BARBAR
%left AND AMPERAMPER
%left NOT
%nonassoc EQ LT GT LTE GTE NEQ
%left MINUS PLUS
%left MULT DIV MOD
%left p_uminus
%left POWER
%left PRE
%nonassoc RBRACKET
%nonassoc LBRACKET

%start <Lustre_types.top_decl list> prog

%start <Lustre_types.top_decl list> header

%start <Lustre_types.expr_annot> lustre_annot

%start <Lustre_types.spec_types> lustre_spec

%%

ident:
| x=UIDENT { x }
| x=IDENT  { x }

module_ident:
| m=ident { m }

file_ident:
| m=module_ident                    { m }
| m=module_ident POINT f=file_ident { m ^ "." ^ f }

path_ident:
| POINT DIV p=path_ident        { "./" ^ p }
| f=file_ident DIV p=path_ident { f ^ "/" ^ p }
| DIV p=path_ident              { "/" ^ p }
| f=file_ident                  { f }

tag_bool:
| TRUE  { tag_true }
| FALSE { tag_false }

tag_ident:
| t=UIDENT   { t }
| t=tag_bool { t }

node_ident:
| n=ident { n }

node_ident_decl:
| n=node_ident { push_node n }

vdecl_ident:
| x=ident { mkident x }

const_ident:
| c=ident { c }

type_ident:
| t=IDENT { t }

prog:
| p=prefix ds=flatten(top_decl*) EOF { List.map ((|>) false) p @ ds }

header:
| p=prefix ds=flatten(top_decl_header*) EOF { List.map ((|>) true) p @ ds }

prefix:
|                      { [] }
| o=open_lusi p=prefix { (fun _ -> o) :: p }
| td=typ_def p=prefix  { (fun is_header -> td is_header) :: p }

open_lusi:
| OPEN QUOTE p=path_ident QUOTE    { mktop_decl false (Open (true, p)) }
| INCLUDE QUOTE p=path_ident QUOTE { mktop_decl false (Include p) }
| OPEN LT p=path_ident GT          { mktop_decl false (Open (false, p))  }

state_annot:
| FUNCTION { true }
| NODE     { false }

top_decl_header:
| CONST ds=cdecl+ SCOL
  { List.map ((|>) true) ds }
| nodei_spec=nodespecs nodei_stateless=state_annot nodei_id=node_ident_decl
  LPAR nodei_inputs=var_decl_list(vdecl) RPAR
  RETURNS LPAR nodei_outputs=var_decl_list(vdecl) RPAR
  nodei_prototype=preceded(PROTOTYPE, node_ident)?
  nodei_in_lib=preceded(LIB, module_ident)* SCOL
  { let nd = mktop_decl true (ImportedNode {
                                  nodei_id;
                                  nodei_type = Types.new_var ();
                                  nodei_clock = Clocks.new_var true;
                                  nodei_inputs;
                                  nodei_outputs;
                                  nodei_stateless;
                                  nodei_spec;
                                  nodei_prototype;
                                  nodei_in_lib
               })
    in
    pop_node ();
    [nd]
  }
| c=top_contract
  { [c] }

top_decl:
| CONST ds=cdecl+ SCOL
  { List.map ((|>) false) ds }
| node_dec_stateless=state_annot node_id=node_ident_decl
  LPAR node_inputs=var_decl_list(vdecl) RPAR
  RETURNS LPAR node_outputs=var_decl_list(vdecl) RPAR SCOL?
  node_spec=nodespecs
  node_locals=locals LET content=stmt_list TEL
  { let node_stmts, node_asserts, node_annot = content in
    (* Declaring eqs annots *)
    List.iter (fun ann ->
        List.iter (fun (key, _) ->
            Annotations.add_node_ann node_id key)
          ann.annots)
      node_annot;
    (* Building the node *)
    let nd = mktop_decl false (Node
                                 {node_id;
                                  node_type = Types.new_var ();
                                  node_clock = Clocks.new_var true;
                                  node_inputs;
                                  node_outputs;
                                  node_locals;
                                  node_gencalls = [];
                                  node_checks = [];
                                  node_asserts;
                                  node_stmts;
                                  node_dec_stateless;
                                  node_stateless = None;
                                  node_spec;
                                  node_annot;
                                  node_iscontract = false;
               })
    in
    pop_node ();
    (*add_node $3 nd;*)
    [nd]
  }
| s=NODESPEC
  { match s with
    | LocalContract _ -> assert false
    | TopContract c   -> c
  }

nodespecs:
| ss=nodespec_list
  { match ss with
    | None   -> None
    | Some c -> Some (Contract c)
  }

nodespec_list:
| { None }
| s=NODESPEC ss=nodespec_list
  { let extract x = match x with LocalContract c -> c | _ -> assert false in
    let s1 = extract s in
    match ss with
    | None -> Some s1
    | Some s2 -> Some (merge_contracts s1 s2)
  }

typ_def:
| TYPE tydef_id=type_ident EQ tydef_desc=typ_def_rhs SCOL
  { fun itf ->
    let typ = mktop_decl itf (TypeDef { tydef_id; tydef_desc }) in
    (*add_type itf $2 typ;*)
    typ
  }

typ_def_rhs:
| t=typeconst
  { t }
| ENUM LCUR ts=separated_nonempty_list(COMMA, UIDENT) RCUR
  { Tydec_enum ts }
| STRUCT LCUR fs=separated_list(SCOL, separated_pair(IDENT, COL, typeconst)) RCUR
  { Tydec_struct fs }

%inline array_typ_decl:
|                          { [] }
| ds=preceded(POWER, dim)+ { ds }

typeconst:
| TINT ds=array_typ_decl         { mkarraytype Tydec_int ds }
| TBOOL ds=array_typ_decl        { mkarraytype Tydec_bool ds }
| TREAL ds=array_typ_decl        { mkarraytype Tydec_real ds }
/* | TFLOAT ds=array_typ_decl { mkarraytype Tydec_float ds } */
| t=type_ident ds=array_typ_decl { mkarraytype (Tydec_const t) ds }
| TBOOL TCLOCK                   { Tydec_clock Tydec_bool }
| t=IDENT TCLOCK                 { Tydec_clock (Tydec_const t) }

stmt_list:
| { [], [], [] }
| e=eq ss=stmt_list
  { let eql, assertl, annotl = ss in
    Eq e :: eql, assertl, annotl
  }
| a=assert_ ss=stmt_list
  { let eql, assertl, annotl = ss in
    eql, a :: assertl, annotl
  }
| a=ANNOT ss=stmt_list
  { let eql, assertl, annotl = ss in
    eql, assertl, a :: annotl
  }
| a=automaton ss=stmt_list
  { let eql, assertl, annotl = ss in
    Aut a :: eql, assertl, annotl
  }

automaton:
| AUTOMATON t=type_ident hs=handler* { Automata.mkautomata (get_loc ()) t hs }

handler:
| STATE x=UIDENT COL ul=unless* l=locals LET ss=stmt_list TEL ut=until*
  { Automata.mkhandler (get_loc ()) x ul ut l ss }

unless:
| UNLESS e=expr RESTART s=UIDENT { get_loc (), e, true, s  }
| UNLESS e=expr RESUME s=UIDENT  { get_loc (), e, false, s }

until:
| UNTIL e=expr RESTART s=UIDENT { get_loc (), e, true, s }
| UNTIL e=expr RESUME s=UIDENT  { get_loc (), e, false, s }

assert_:
| ASSERT e=expr SCOL { mkassert e }

eq:
| xs=pattern EQ e=expr SCOL {mkeq (List.map fst xs, e)}

%inline pattern:
| xs=ident_list           { xs }
| LPAR xs=ident_list RPAR { xs }

lustre_spec:
| cs=top_contract+ EOF   { TopContract cs }
| c=contract_content EOF { LocalContract c }

top_contract:
| CONTRACT node_id=node_ident_decl
  LPAR node_inputs=var_decl_list(vdecl) RPAR
  RETURNS LPAR node_outputs=var_decl_list(vdecl) RPAR SCOL?
  LET cc=contract_content TEL
  { let nd = mktop_decl true (Node {
                                  node_id;
                                  node_type = Types.new_var ();
                                  node_clock = Clocks.new_var true;
                                  node_inputs;
                                  node_outputs;
                                  node_locals = []; (* will be filled later *)
                                  node_gencalls = [];
                                  node_checks = [];
                                  node_asserts = [];
                                  node_stmts = []; (* will be filled later *)
                                  node_dec_stateless = false;
                                  (* By default we assume contracts as stateful *)
                                  node_stateless = None;
                                  node_spec = Some (Contract cc);
                                  node_annot = [];
                                  node_iscontract = true;
                                }
               )
    in
    pop_node ();
    (*add_imported_node $3 nd;*)
    nd
  }

contract_content:
| { empty_contract }
| CONTRACT cc=contract_content
  { cc }
| CONST x=IDENT COL t=typeconst? EQ e=expr SCOL cc=contract_content
  { merge_contracts (mk_contract_var x true (mkotyp t) e (get_loc())) cc }
| VAR x=IDENT COL t=typeconst EQ e=expr SCOL cc=contract_content
  { merge_contracts (mk_contract_var x false (Some (mktyp t)) e (get_loc())) cc }
| ASSUME x=ioption(STRING) e=qexpr SCOL cc=contract_content
  { merge_contracts (mk_contract_assume x e) cc }
| GUARANTEES x=ioption(STRING) e=qexpr SCOL cc=contract_content
  { merge_contracts (mk_contract_guarantees x e) cc }
| MODE x=IDENT LPAR mc=mode_content RPAR SCOL cc=contract_content
  { merge_contracts (
        let r, e = mc in
        mk_contract_mode x r e (get_loc())) cc
  }
| IMPORT x=IDENT LPAR xs=expr_or_tuple RPAR RETURNS LPAR ys=expr_or_tuple RPAR
  SCOL cc=contract_content
  { merge_contracts (mk_contract_import x xs ys (get_loc())) cc }

%inline expr_or_tuple:
| e=expr                     { e }
| e=expr COMMA es=array_expr { mkexpr (Expr_tuple (e :: es)) }

mode_content:
| { [], [] }
| REQUIRE eexpr_name=ioption(STRING) qe=qexpr SCOL mc=mode_content
  { let (r, e) = mc in
    { qe with eexpr_name } :: r, e }
| ENSURE eexpr_name=ioption(STRING) qe=qexpr SCOL mc=mode_content
  { let (r, e) = mc in
    r, { qe with eexpr_name } :: e }

(* /* WARNING: UNUSED RULES */
 * tuple_qexpr:
 * | qexpr COMMA qexpr {[$3;$1]}
 * | tuple_qexpr COMMA qexpr {$3::$1} *)

qexpr:
| e=expr                      { mkeexpr e }
  /* Quantifiers */
| EXISTS x=vdecl SCOL e=qexpr { extend_eexpr [Exists, x] e }
| FORALL x=vdecl SCOL e=qexpr { extend_eexpr [Forall, x] e }

(* %inline tuple_expr:
 * | e=expr COMMA es=array_expr { e :: es } *)

// Same as tuple expr but accepting lists with single element
%inline array_expr:
| es=separated_nonempty_list(COMMA, expr) { es }

expr:
/* constants */
| c=INT                   { mkexpr (Expr_const (Const_int c)) }
| c=REAL                  { mkexpr (Expr_const (Const_real c)) }
| c=STRING %prec p_string { mkexpr (Expr_const (Const_string c)) }
| COLCOL c=IDENT          { mkexpr (Expr_const (Const_modeid c)) }
/* | c=FLOAT { mkexpr (Expr_const (Const_float c)) }*/

/* Idents or type enum tags */
| x=IDENT    { mkexpr (Expr_ident x) }
| x=UIDENT   { mkexpr (Expr_ident x) (* TODO we will differenciate enum constants from variables later *) }
| t=tag_bool { mkexpr (Expr_const (Const_tag t)) } (* on sept 2014, X changed the Const to
                                                      mkexpr (Expr_ident $1)
                                                      reverted back to const on july 2019 *)
| LPAR a=ANNOT e=expr RPAR  { update_expr_annot (get_current_node ()) e a }
| LPAR e=expr_or_tuple RPAR { e }

/* Array expressions */
| LBRACKET es=array_expr RBRACKET
  { mkexpr (Expr_array es) }
| e=expr POWER d=dim
  { mkexpr (Expr_power (e, d)) }
| e=expr ds=delimited(LBRACKET, dim, RBRACKET)+
  { List.fold_left (fun base d -> mkexpr (Expr_access (base, d))) e ds }

/* Temporal operators */
| PRE e=expr
  { mkexpr (Expr_pre e) }
| e1=expr ARROW e2=expr
  { mkexpr (Expr_arrow (e1, e2)) }
| e1=expr FBY e2=expr
  { mkexpr (Expr_arrow (e1, mkexpr (Expr_pre e2))) }
| e=expr WHEN x=vdecl_ident
  { mkexpr (Expr_when (e, fst x, tag_true)) }
| e=expr WHENNOT x=vdecl_ident
  { mkexpr (Expr_when (e, fst x, tag_false)) }
| e=expr WHEN t=tag_ident LPAR x=vdecl_ident RPAR
  { mkexpr (Expr_when (e, fst x, t)) }
| MERGE x=vdecl_ident
  hs=delimited(LPAR, separated_pair(tag_ident, ARROW, expr), RPAR)*
  { mkexpr (Expr_merge (fst x, hs)) }

/* Applications */
| f=node_ident LPAR es=expr_or_tuple RPAR r=preceded(EVERY, expr)?
  { match f, es.expr_desc, r with
    | "fbyn", Expr_tuple [expr; n; init], None ->
       let n = match n.expr_desc with
         | Expr_const (Const_int n) -> n
         | _ -> assert false
       in
       fby expr n init
    | "fbyn", _ , Some _ ->
       assert false (* TODO Ca veut dire quoi fby (e,n,init) every c *)
    | _ -> mkexpr (Expr_appl (f, es, r))
  }

/* Boolean expr */
| e1=expr AND e2=expr         { mkpredef_call_b "&&" e1 e2 }
| e1=expr AMPERAMPER e2=expr  { mkpredef_call_b "&&" e1 e2 }
| e1=expr OR e2=expr          { mkpredef_call_b "||" e1 e2 }
| e1=expr BARBAR e2=expr      { mkpredef_call_b "||" e1 e2 }
| e1=expr XOR e2=expr         { mkpredef_call_b "xor" e1 e2 }
| NOT e=expr                  { mkpredef_call_u "not" e }
| e1=expr IMPL e2=expr        { mkpredef_call_b "impl" e1 e2 }

/* Comparison expr */
| e1=expr EQ e2=expr          { mkpredef_call_b "=" e1 e2 }
| e1=expr LT e2=expr          { mkpredef_call_b "<" e1 e2 }
| e1=expr LTE e2=expr         { mkpredef_call_b "<=" e1 e2 }
| e1=expr GT e2=expr          { mkpredef_call_b ">" e1 e2 }
| e1=expr GTE e2=expr         { mkpredef_call_b ">=" e1 e2 }
| e1=expr NEQ e2=expr         { mkpredef_call_b "!=" e1 e2 }

/* Arithmetic expr */
| e1=expr PLUS e2=expr        { mkpredef_call_b "+" e1 e2 }
| e1=expr MINUS e2=expr       { mkpredef_call_b "-" e1 e2 }
| e1=expr MULT e2=expr        { mkpredef_call_b "*" e1 e2 }
| e1=expr DIV e2=expr         { mkpredef_call_b "/" e1 e2 }
| MINUS e=expr %prec p_uminus { mkpredef_call_u "uminus" e }
| e1=expr MOD e2=expr         { mkpredef_call_b "mod" e1 e2 }

/* If */
| IF e=expr THEN t=expr ELSE f=expr { mkexpr (Expr_ite (e, t, f)) }

signed_const:
| c=INT
  { Const_int c }
| c=REAL
  { Const_real c }
/* | c=FLOAT { Const_float c } */
| t=tag_ident { Const_tag t }
| MINUS c=INT
  { Const_int (-1 * c) }
| MINUS c=REAL
  { Const_real (Real.uminus c) }
/* | MINUS c=FLOAT { Const_float (-1. *. c) } */
| LCUR
  cs=separated_nonempty_list(COMMA, separated_pair(IDENT, EQ, signed_const))
  RCUR
  { Const_struct cs }
| LBRACKET cs=separated_nonempty_list(COMMA, signed_const) RBRACKET
  { Const_array cs }

dim:
| i=INT                      { mkdim_int i }
| LPAR d=dim RPAR            { d }
| x=ident                    { mkdim_ident x }
| d1=dim AND d2=dim          { mkdim_appl_b "&&" d1 d2 }
| d1=dim AMPERAMPER d2=dim   { mkdim_appl_b "&&" d1 d2 }
| d1=dim OR d2=dim           { mkdim_appl_b "||" d1 d2 }
| d1=dim BARBAR d2=dim       { mkdim_appl_b "||" d1 d2 }
| d1=dim XOR d2=dim          { mkdim_appl_b "xor" d1 d2 }
| NOT d=dim                  { mkdim_appl_u "not" d }
| d1=dim IMPL d2=dim         { mkdim_appl_b "impl" d1 d2 }

/* Comparison dim */
| d1=dim EQ d2=dim           { mkdim_appl_b "=" d1 d2 }
| d1=dim LT d2=dim           { mkdim_appl_b "<" d1 d2 }
| d1=dim LTE d2=dim          { mkdim_appl_b "<=" d1 d2 }
| d1=dim GT d2=dim           { mkdim_appl_b ">" d1 d2 }
| d1=dim GTE  d2=dim         { mkdim_appl_b ">=" d1 d2 }
| d1=dim NEQ d2=dim          { mkdim_appl_b "!=" d1 d2 }

/* Arithmetic dim */
| d1=dim PLUS d2=dim         { mkdim_appl_b "+" d1 d2 }
| d1=dim MINUS d2=dim        { mkdim_appl_b "-" d1 d2 }
| d1=dim MULT d2=dim         { mkdim_appl_b "*" d1 d2 }
| d1=dim DIV d2=dim          { mkdim_appl_b "/" d1 d2 }
| MINUS d=dim %prec p_uminus { mkdim_appl_u "uminus" d }
| d1=dim MOD d2=dim          { mkdim_appl_b "mod" d1 d2 }

/* If */
| IF d=dim THEN t=dim ELSE f=dim { mkdim_ite d t f }

%inline locals:
| xs=loption(preceded(VAR, var_decl_list(local_vdecl))) { xs }

var_decl_list(X):
| d=X ioption(SCOL)            { d }
| d=X SCOL ds=var_decl_list(X) { d @ ds }

vdecl:
| xs=ident_list COL t=typeconst c=clock?
  { mkvdecls false (Some t) c None xs }
| CONST xs=ident_list t=preceded(COL, typeconst)?
  /* static parameters don't have clocks */
  { mkvdecls true t None None xs }

local_vdecl:
| xs=ident_list /* Useless no ?*/
  { mkvdecls false None None None xs }
| xs=ident_list COL t=typeconst c=clock?
  { mkvdecls false (Some t) c None xs }
| CONST x=vdecl_ident t=preceded(COL, typeconst)? EQ e=expr
  /* static parameters don't have clocks */
  { mkvdecls true t None (Some e) [x] }

cdecl:
| x=const_ident EQ c=signed_const
  { fun itf ->
    let c = mktop_decl itf (Const {
                                const_id = x;
                                const_loc = get_loc ();
                                const_type = Types.new_var ();
                                const_value = c
              })
    in
    (*add_const itf $1 c;*)
    c
  }

%inline clock:
| l=when_cond+ { mkclock (Ckdec_bool l) }

when_cond:
| WHEN x=IDENT                       { x, tag_true }
| WHENNOT x=IDENT                    { x, tag_false }
| WHEN t=tag_ident LPAR x=IDENT RPAR { x, t }

%inline ident_list:
| ds=separated_nonempty_list(COMMA, vdecl_ident) { ds }

lustre_annot:
| lustre_annot_list EOF { { annots = $1; annot_loc = get_loc () } }

lustre_annot_list:
  { [] } 
| kwd COL qexpr SCOL lustre_annot_list { ($1,$3)::$5 }
| IDENT COL qexpr SCOL lustre_annot_list { ([$1],$3)::$5 }
| INVARIANT COL qexpr SCOL lustre_annot_list{ (["invariant"],$3)::$5 }
// (* | OBSERVER COL qexpr SCOL lustre_annot_list { (["observer"],$3)::$5 } *)
| CCODE COL qexpr SCOL lustre_annot_list{ (["c_code"],$3)::$5 }
| MATLAB COL qexpr SCOL lustre_annot_list{ (["matlab"],$3)::$5 }


kwd:
DIV { [] }
| DIV IDENT kwd { $2::$3}

%%
(* Local Variables: *)
(* compile-command:"make -C .." *)
(* End: *)


