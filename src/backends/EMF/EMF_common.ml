open Lustre_types
open Machine_code_types
module VSet = Corelang.VSet
open Format
open Machine_code_common

(* Matlab starting counting from 1.
   simple function to extract the element id in the list. Starts from 1. *)
let rec get_idx x l =
  match l with
  | hd::tl -> if hd = x then 1 else 1+(get_idx x tl)
  | [] -> assert false

let rec get_expr_vars v =
  match v.value_desc with
  | Cst c -> VSet.empty
  | Var v -> VSet.singleton v
  | Fun (_, args) -> List.fold_left (fun accu v -> VSet.union accu (get_expr_vars v)) VSet.empty args
  | _ -> assert false (* Invalid argument *)

let is_imported_node f m =
  let (decl, _) = List.assoc f m.mcalls in
  Corelang.is_imported_node decl

(* Handling of enumerated types: for the moment each of such type is transformed
   into an int: the idx number of the constant in the typedef. This is not so
   nice but is compatible with basic Simulink types: int, real, bools) *)
(*
let recorded_enums = ref []
let record_types prog =
  let typedefs = Corelang.get_typedefs prog in
  List.iter (fun top ->
    let consts = consts_of_enum_type top in
  ) prog
*)
    
(* Basic printing functions *)

let hash_map = Hashtbl.create 13
  
(* If string length of f is longer than 50 chars, we select the 10 first and
   last and put a hash in the middle *)
let print_protect fmt f =
  fprintf str_formatter "%t" f;
  let s = flush_str_formatter () in
  let l = String.length s in
  if l > 30 then
    (* let _ = Format.eprintf "Looking for variable %s in hash @[<v 0>%t@]@." *)
    (*   s *)
    (*   (fun fmt -> Hashtbl.iter (fun s new_s -> fprintf fmt "%s -> %s@ " s new_s) hash_map) *)
    (* in *)
    if Hashtbl.mem hash_map s then
    fprintf fmt "%s" (Hashtbl.find hash_map s)
    else
      let prefix = String.sub s 0 10 and
	  suffix = String.sub s (l-10) 10 in
      let hash = Hashtbl.hash s in
      fprintf str_formatter "%s_%i_%s" prefix hash suffix;
      let new_s = flush_str_formatter () in
      Hashtbl.add hash_map s new_s;
      fprintf fmt "%s" new_s
  else
    fprintf fmt "%s" s
    
let pp_var_string fmt v =fprintf fmt "\"%t\"" (fun fmt -> print_protect fmt (fun fmt -> fprintf fmt "%s" v)) 
let pp_var_name fmt v = print_protect fmt (fun fmt -> Printers.pp_var_name fmt v) 
(*let pp_node_args = fprintf_list ~sep:", " pp_var_name*)

(********* Printing types ***********)
(* Two cases:
   - printing a variable definition:
     -  we look at the declared type if available
     - if not, we print the inferred type

   - printing a constant definion
*)
  
  

let rec pp_emf_dim fmt dim_expr =
  fprintf fmt "{";
  (let open Dimension in
   match dim_expr.dim_desc with
   | Dbool b -> fprintf fmt "\"kind\": \"bool\",@ \"value\": \"%b\"" b
   | Dint i -> fprintf fmt "\"kind\": \"int\",@ \"value\": \"%i\"" i
   | Dident s -> fprintf fmt "\"kind\": \"ident\",@ \"value\": \"%s\"" s
   | Dappl(f, args) -> fprintf fmt "\"kind\": \"fun\",@ \"id\": \"%s\",@ \"args\": [@[%a@]]"
                         f (Utils.fprintf_list ~sep:",@ " pp_emf_dim) args 
   | Dite(i,t,e) -> fprintf fmt "\"kind\": \"ite\",@ \"guard\": \"%a\",@ \"then\": %a,@ \"else\": %a"
                      pp_emf_dim i pp_emf_dim t pp_emf_dim e 
   | Dlink e -> pp_emf_dim fmt e
   | Dvar
   | Dunivar -> assert false (* unresolved *)
  );
  fprintf fmt "}"

     


(* First try to print the declared one *)
let rec pp_concrete_type dec_t infered_t fmt =
  match dec_t with
  | Tydec_any -> (* Dynamical built variable. No declared type. Shall
                    use the infered one. *)
     pp_infered_type fmt infered_t
  | Tydec_int -> fprintf fmt "{ \"kind\": \"int\" }" (* !Options.int_type *)
  | Tydec_real -> fprintf fmt "{ \"kind\": \"real\" }" (* !Options.real_type *)
  (* TODO we could add more concrete types here if they were available in
     dec_t *)
  | Tydec_bool -> fprintf fmt "{ \"kind\": \"bool\" }"
  | Tydec_clock t -> pp_concrete_type t infered_t fmt
  | Tydec_const id -> (
    (* This is an alias type *)

    (* id for a enumerated type, eg. introduced by automata *)
    let typ = (Corelang.typedef_of_top (Hashtbl.find Corelang.type_table dec_t)) in
    (* Print the type name associated to this enumerated type. This is
       basically an integer *)
    pp_tag_type id typ infered_t fmt
  )
                    
  | Tydec_struct _ | Tydec_enum _ ->
     assert false (* should not happen. These type are only built when
                     declaring a type in the prefix of the lustre
                     file. They shall not be associated to variables
                   *)
    
  | Tydec_array (dim, e) -> (
    let inf_base = match infered_t.Typing.tdesc with
      | Typing.Tarray(_,t) -> t
      | _ ->   (* returing something useless, hoping that the concrete
                  datatype will return something usefull *)
         Typing.new_var ()
    in
    fprintf fmt "{ \"kind\": \"array\", \"base_type\": %t, \"dim\": %a }"
      (pp_concrete_type e inf_base)
      pp_emf_dim dim
  )
                          
(* | _ -> eprintf
 *          "unhandled construct in type printing for EMF backend: %a@."
 *          Printers.pp_var_type_dec_desc dec_t; raise (Failure "var") *)
and pp_tag_type id typ inf fmt =
  (* We ought to represent these types as values: enum will become int, we keep the name for structs *)
  let rec aux tydec_desc =
    match tydec_desc with  
    | Tydec_int 
      | Tydec_real 
      | Tydec_bool
      | Tydec_array _ -> pp_concrete_type tydec_desc inf fmt
    | Tydec_const id ->
       (* Alias of an alias: unrolling definitions *)
       let typ = (Corelang.typedef_of_top
                    (Hashtbl.find Corelang.type_table tydec_desc))
       in
       pp_tag_type id typ inf fmt
       
    | Tydec_clock ty -> aux ty
    | Tydec_enum const_list -> ( (* enum can be mapped to int *)
      let size = List.length const_list in
      fprintf fmt "{ \"name\": \"%s\", \"kind\": \"enum\", \"size\": \"%i\" }" id size
    )
    | Tydec_struct _ ->
       fprintf fmt "{ \"name\": \"%s\", \"kind\": \"struct\" }" id
    | Tydec_any -> (* shall not happen: a declared type cannot be
                      bound to type any *)
       assert false
  in
  aux typ.tydef_desc
and pp_infered_type fmt t =
  (* Shall only be used for variable types that were not properly declared. Ie generated at compile time. *)
  let open Types in
  if is_bool_type t  then fprintf fmt "{ \"kind\": \"bool\" }" else
    if is_int_type t then fprintf fmt "{ \"kind\": \"int\" }" else (* !Options.int_type *)
      if is_real_type t then fprintf fmt "{ \"kind\": \"real\" }" else (* !Options.real_type *)
        match t.tdesc with
        | Tclock t ->
           pp_infered_type fmt t
        | Tstatic (_, t) ->
           fprintf fmt "%a" pp_infered_type t
        | Tconst id ->
           (* This is a type id for a enumerated type, eg. introduced by automata *)
           let typ =
             (Corelang.typedef_of_top
                (Hashtbl.find Corelang.type_table (Tydec_const id)))
           in
           pp_tag_type id typ t fmt
        | Tlink ty -> 
           pp_infered_type fmt ty
        | Tarray (dim, base_t) ->
           fprintf fmt "{ \"kind\": \"array\", \"base_type\": %a, \"dim\": %a }"
             pp_infered_type base_t
             pp_emf_dim dim
    | _ -> eprintf "unhandled type: %a@." Types.print_node_ty t; assert false

(*let pp_cst_type fmt v =
  match v.value_desc with
  | Cst c-> pp_cst_type c v.value_type fmt (* constants do not have declared type (yet) *)
  | _ -> assert false
*)

(* Provide both the declared type and the infered one. *)
let pp_var_type fmt v =
  try
    if Machine_types.is_specified v then
      Machine_types.pp_var_type fmt v
    else
      pp_concrete_type v.var_dec_type.ty_dec_desc v.var_type fmt
  with Failure msg -> eprintf "failed var: %a@.%s@." Printers.pp_var v msg; assert false
    
(******** Other print functions *)

let pp_emf_list ?(eol:('a, formatter, unit) Pervasives.format="") pp fmt l =
  match l with
    [] -> ()
  | _ -> fprintf fmt "@[";
         Utils.fprintf_list ~sep:",@ " pp fmt l;
         fprintf fmt "@]%(%)" eol
  
(* Print the variable declaration *)
let pp_emf_var_decl fmt v =
  fprintf fmt "@[{\"name\": \"%a\", \"datatype\": %a, \"original_name\": \"%a\"}@]"
    pp_var_name v
    pp_var_type v
    Printers.pp_var_name v

let pp_emf_vars_decl = pp_emf_list pp_emf_var_decl

 
  
let reset_name id =
  "reset_" ^ id
  
let pp_tag_id fmt t =
  let typ = (Corelang.typedef_of_top (Hashtbl.find Corelang.tag_table t)) in
  if typ.tydef_id = "bool" then
    pp_print_string fmt t
  else
    let const_list = match typ.tydef_desc with Tydec_enum tl -> tl | _ -> assert false in
    fprintf fmt "%i" (get_idx t const_list)

let pp_cst_type c inf fmt (*infered_typ*) =
  let pp_basic fmt s = fprintf fmt "{ \"kind\": \"%s\" }" s in
  match c with
  | Const_tag t ->
     let typ = (Corelang.typedef_of_top (Hashtbl.find Corelang.tag_table t)) in
     if typ.tydef_id = "bool" then
       pp_basic fmt "bool"
     else
       pp_tag_type t typ inf fmt
  | Const_int _ -> pp_basic fmt "int" (*!Options.int_type*)
  | Const_real _ -> pp_basic fmt "real" (*!Options.real_type*)
  | Const_string _ -> pp_basic fmt "string" 
  | _ -> eprintf "cst: %a@." Printers.pp_const c; assert false

    
let pp_emf_cst c inf fmt =
  let pp_typ fmt = 
    fprintf fmt "\"datatype\": %t@ "
      (pp_cst_type c inf)   
  in
  match c with
  | Const_tag t->
     let typ = (Corelang.typedef_of_top (Hashtbl.find Corelang.tag_table t)) in
     if typ.tydef_id = "bool" then (
       fprintf fmt "{@[\"type\": \"constant\",@ ";
       fprintf fmt"\"value\": \"%a\",@ "
	 Printers.pp_const c;
       pp_typ fmt;
       fprintf fmt "@]}"
     )
     else (
       fprintf fmt "{@[\"type\": \"constant\",@ \"value\": \"%a\",@ " 
	 pp_tag_id t;
       fprintf fmt "\"origin_type\": \"%s\",@ \"origin_value\": \"%s\",@ "
	 typ.tydef_id t;
       pp_typ fmt;
       fprintf fmt "@]}"
     )
  | Const_string s ->
     fprintf fmt "{@[\"type\": \"constant\",@ \"value\": \"%s\",@ " s;
     pp_typ fmt;
     fprintf fmt "@]}"
     
  | _ -> (
    fprintf fmt "{@[\"type\": \"constant\",@ \"value\": \"%a\",@ "
      Printers.pp_const c;
    pp_typ fmt;
    fprintf fmt "@]}"
  )
  
(* Print a value: either a constant or a variable value *)
let rec pp_emf_cst_or_var m fmt v =
  match v.value_desc with
  | Cst c -> pp_emf_cst c v.value_type fmt 
  | Var v -> (
    fprintf fmt "{@[\"type\": \"variable\",@ \"value\": \"%a\",@ "
      pp_var_name v;
    (*    fprintf fmt "\"original_name\": \"%a\",@ " Printers.pp_var_name v; *)
    fprintf fmt "\"datatype\": %a@ " pp_var_type v;
    fprintf fmt "@]}"
  )
  | Array vl -> (
     fprintf fmt "{@[\"type\": \"array\",@ \"value\": @[[%a@]]@ "
      (pp_emf_cst_or_var_list m) vl;
     fprintf fmt "@]}"
  )
  | Access (arr, idx) -> (
      fprintf fmt "{@[\"type\": \"array access\",@ \"array\": @[[%a@]],@ \"idx\": @[[%a@]]@ "
      (pp_emf_cst_or_var m) arr (pp_emf_cst_or_var m) idx;
     fprintf fmt "@]}"
  )
  | Power (v,nb) ->(
      fprintf fmt "{@[\"type\": \"power\",@ \"expr\": @[[%a@]],@ \"nb\": @[[%a@]]@ "
      (pp_emf_cst_or_var m) v (pp_emf_cst_or_var m) nb;
     fprintf fmt "@]}"
  )
  | Fun _ -> eprintf "Fun expression should have been normalized: %a@." (pp_val m) v ; assert false (* Invalid argument *)

and pp_emf_cst_or_var_list m =
  Utils.fprintf_list ~sep:",@ " (pp_emf_cst_or_var m)

(* Printer lustre expr and eexpr *)
    
let rec pp_emf_expr fmt e =
  match e.expr_desc with
  | Expr_const c -> pp_emf_cst c e.expr_type fmt 
  | Expr_ident id ->
     fprintf fmt "{@[\"type\": \"variable\",@ \"value\": \"%a\",@ "
       print_protect (fun fmt -> pp_print_string fmt id);
    fprintf fmt "\"datatype\": %t@ "
      (pp_concrete_type
	 Tydec_any (* don't know much about that time since it was not
		      declared. That may not work with clock constants *)
	 e.expr_type
      );
    fprintf fmt "@]}"

  | Expr_tuple el ->
     fprintf fmt "[@[<hov 0>%a@ @]]"
       (Utils.fprintf_list ~sep:",@ " pp_emf_expr) el
 (* Missing these 
  | Expr_ite   of expr * expr * expr
  | Expr_arrow of expr * expr
  | Expr_fby of expr * expr
  | Expr_array of expr list
  | Expr_access of expr * Dimension.dim_expr
  | Expr_power of expr * Dimension.dim_expr
  | Expr_pre of expr
  | Expr_when of expr * ident * label
  | Expr_merge of ident * (label * expr) list
  | Expr_appl of call_t
  *)
  | _ -> (
    Log.report ~level:2
      (fun fmt ->
	fprintf fmt "Warning: unhandled expression %a in annotation.@ "
	  Printers.pp_expr e;
 	fprintf fmt "Will not be produced in the experted JSON EMF@."
      );    
    fprintf fmt "\"unhandled construct, complain to Ploc\""
  )
(* Remaining constructs *)  
(* | Expr_ite   of expr * expr * expr *)
(* | Expr_arrow of expr * expr *)
(* | Expr_fby of expr * expr *)
(* | Expr_array of expr list *)
(* | Expr_access of expr * Dimension.dim_expr *)
(* | Expr_power of expr * Dimension.dim_expr *)
(* | Expr_pre of expr *)
(* | Expr_when of expr * ident * label *)
(* | Expr_merge of ident * (label * expr) list *)
(* | Expr_appl of call_t *)

let pp_emf_exprs = pp_emf_list pp_emf_expr
       
let pp_emf_const fmt v =
  fprintf fmt "@[<hov 0>{\"name\": \"%a\",@ \"datatype\":%a,@ \"original_name\": \"%a\",@ \"value\": %a}@]"
    pp_var_name v
    pp_var_type v
    Printers.pp_var_name v
    pp_emf_expr (match v.var_dec_value with None -> assert false | Some e -> e)

let pp_emf_consts = pp_emf_list pp_emf_const
                  
let pp_emf_eexpr fmt ee =
  fprintf fmt "{@[<hov 0>%t\"quantifiers\": \"%a\",@ \"qfexpr\": @[%a@]@] }"
    (fun fmt -> match ee.eexpr_name with
                | None -> ()
                | Some name -> Format.fprintf fmt "\"name\": \"%s\",@ " name
    )
    (Utils.fprintf_list ~sep:"; " Printers.pp_quantifiers)
    ee.eexpr_quantifiers
    pp_emf_expr ee.eexpr_qfexpr

let pp_emf_eexprs = pp_emf_list pp_emf_eexpr

(*
                      TODO Thanksgiving

                      trouver un moyen de transformer en machine code les instructions de chaque spec
                      peut etre associer a chaque imported node une minimachine
                      et rajouter un champ a spec dans machine code pour stoquer memoire et instr
 *)                
                 
let pp_emf_stmt fmt stmt =
  match stmt with
  | Aut _ -> assert false
  | Eq eq -> (
    fprintf fmt "@[ @[<v 2>\"%a\": {@ " (Utils.fprintf_list ~sep:"_" pp_print_string) eq.eq_lhs;
    fprintf fmt "\"lhs\": [%a],@ " (Utils.fprintf_list ~sep:", " (fun fmt vid -> fprintf fmt "\"%s\"" vid)) eq.eq_lhs;
    fprintf fmt "\"rhs\": %a,@ " pp_emf_expr eq.eq_rhs;
    fprintf fmt "@]@]@ }"
  )

let pp_emf_stmts = pp_emf_list pp_emf_stmt 
  
(* Printing the type declaration, not its use *)
let rec pp_emf_typ_dec fmt tydef_dec =
  fprintf fmt "{";
  (match tydef_dec with
   | Tydec_any -> fprintf fmt "\"kind\": \"any\""
   | Tydec_int -> fprintf fmt "\"kind\": \"int\""
   | Tydec_real -> fprintf fmt "\"kind\": \"real\""
   | Tydec_bool-> fprintf fmt "\"kind\": \"bool\""
   | Tydec_clock ck -> pp_emf_typ_dec fmt ck
   | Tydec_const c -> fprintf fmt "\"kind\": \"alias\",@ \"value\": \"%s\"" c
   | Tydec_enum el -> fprintf fmt "\"kind\": \"enum\",@ \"elements\": [%a]"
                        (Utils.fprintf_list ~sep:", " (fun fmt e -> fprintf fmt "\"%s\"" e)) el
   | Tydec_struct s -> fprintf fmt "\"kind\": \"struct\",@ \"fields\": [%a]"
                         (Utils.fprintf_list ~sep:", " (fun fmt (id,typ) ->
                              fprintf fmt "\"%s\": %a" id pp_emf_typ_dec typ)) s
   | Tydec_array (dim, typ) -> fprintf fmt "\"kind\": \"array\",@ \"dim\": @[%a@],@ \"base\": %a"
                               pp_emf_dim dim
                               pp_emf_typ_dec typ
  );
  fprintf fmt "}"
 
let pp_emf_typedef fmt typdef_top =
  let typedef = Corelang.typedef_of_top typdef_top in
  fprintf fmt "{ \"%s\": @[%a@] }" typedef.tydef_id pp_emf_typ_dec typedef.tydef_desc 
  
let pp_emf_top_const fmt const_top = 
  let const = Corelang.const_of_top const_top in
  fprintf fmt "{ \"%s\": %t }"
    const.const_id
    (pp_emf_cst const.const_value const.const_type)

(* Local Variables: *)
(* compile-command: "make -C ../.." *)
(* End: *)
