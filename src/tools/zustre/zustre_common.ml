open Lustre_types
open Machine_code_types
open Machine_code_common
open Format
(* open Horn_backend_common
 * open Horn_backend *)
open Zustre_data

module HBC = Horn_backend_common
let node_name = HBC.node_name

let concat = HBC.concat

let rename_machine = HBC.rename_machine
let rename_machine_list = HBC.rename_machine_list

let rename_next = HBC.rename_next
let rename_mid = HBC.rename_mid
let rename_current = HBC.rename_current

let rename_current_list = HBC.rename_current_list
let rename_mid_list = HBC.rename_mid_list
let rename_next_list = HBC.rename_next_list

let full_memory_vars = HBC.full_memory_vars
let inout_vars = HBC.inout_vars
let reset_vars = HBC.reset_vars
let step_vars = HBC.step_vars
let local_memory_vars = HBC.local_memory_vars
let step_vars_m_x = HBC.step_vars_m_x
let step_vars_c_m_x = HBC.step_vars_c_m_x
  
let machine_reset_name = HBC.machine_reset_name 
let machine_step_name = HBC.machine_step_name 
let machine_stateless_name = HBC.machine_stateless_name 

let preprocess = Horn_backend.preprocess
  

exception UnknownFunction of (string * (Format.formatter -> unit))
(** Sorts

A sort is introduced for each basic type and each enumerated type.

A hashtbl records these and allow easy access to sort values, when
   provided with a enumerated type name. 

*)
        
let bool_sort = Z3.Boolean.mk_sort !ctx
let int_sort = Z3.Arithmetic.Integer.mk_sort !ctx
let real_sort = Z3.Arithmetic.Real.mk_sort !ctx


let get_const_sort = Hashtbl.find const_sorts 
let get_sort_elems = Hashtbl.find sort_elems
let get_tag_sort = Hashtbl.find const_tags
  

  
let decl_sorts () =
  Hashtbl.iter (fun typ decl ->
    match typ with
    | Tydec_const var ->
      (match decl.top_decl_desc with
      | TypeDef tdef -> (
	match tdef.tydef_desc with
	| Tydec_enum tl ->
	  let new_sort = Z3.Enumeration.mk_sort_s !ctx var tl in
          Hashtbl.add const_sorts var new_sort;
          Hashtbl.add sort_elems new_sort tl;
          List.iter (fun t -> Hashtbl.add const_tags t new_sort) tl
          
	| _ -> Format.eprintf "Unknown type : %a@.@?" Printers.pp_var_type_dec_desc typ; assert false
      )
      | _ -> assert false
      )
    | _        -> ()) Corelang.type_table

                 
let rec type_to_sort t =
  if Types.is_bool_type t  then bool_sort else
    if Types.is_int_type t then int_sort else 
  if Types.is_real_type t then real_sort else 
  match (Types.repr t).Types.tdesc with
  | Types.Tconst ty       -> get_const_sort ty
  | Types.Tclock t        -> type_to_sort t
  | Types.Tarray(dim,ty)   -> Z3.Z3Array.mk_sort !ctx int_sort (type_to_sort ty)
  | Types.Tstatic(d, ty)-> type_to_sort ty
  | Types.Tarrow _
  | _                     -> Format.eprintf "internal error: pp_type %a@."
                               Types.print_ty t; assert false


(* let idx_var = *)
(*   Z3.FuncDecl.mk_func_decl_s !ctx "__idx__" [] idx_sort  *)
    
(* let uid_var = *)
(*   Z3.FuncDecl.mk_func_decl_s !ctx "__uid__" [] uid_sort  *)

(** Func decls

    Similarly fun_decls are registerd, by their name, into a hashtbl. The
    proposed encoding introduces a 0-ary fun_decl to model variables and
    fun_decl with arguments to declare reset and step predicates.



*)
let register_fdecl id fd = Hashtbl.add decls id fd
let get_fdecl id =
  try
    Hashtbl.find decls id
  with Not_found -> (Format.eprintf "Unable to find func_decl %s@.@?" id; raise Not_found)

let pp_fdecls fmt =
  Format.fprintf fmt "Registered fdecls: @[%a@]@ "
    (Utils.fprintf_list ~sep:"@ " Format.pp_print_string)  (Hashtbl.fold (fun id _ accu -> id::accu) decls [])

    
let decl_var id =
  (* Format.eprintf "Declaring var %s@." id.var_id; *)
  let fdecl = Z3.FuncDecl.mk_func_decl_s !ctx id.var_id [] (type_to_sort id.var_type) in
  register_fdecl id.var_id fdecl;
  fdecl

let idx_sort = int_sort
let uid_sort = Z3.Z3List.mk_sort !ctx (Z3.Symbol.mk_string !ctx "uid_list") int_sort
let uid_conc = 
  let fd = Z3.Z3List.get_cons_decl uid_sort in
  fun head tail -> Z3.FuncDecl.apply fd [head;tail]

let get_instance_uid =
  let hash : (string, int) Hashtbl.t = Hashtbl.create 13 in
  let cpt = ref 0 in
  fun i ->
    let id =
      if Hashtbl.mem hash i then
	Hashtbl.find hash i
      else (
	incr cpt;
	Hashtbl.add hash i !cpt;
	!cpt
      )
    in
    Z3.Arithmetic.Integer.mk_numeral_i !ctx id
  

  
let decl_rel ?(no_additional_vars=false) name args_sorts =
  (* Enriching arg_sorts with two new variables: a counting index and an
     uid *)
  let args_sorts =
    if no_additional_vars then args_sorts else idx_sort::uid_sort::args_sorts in
  
  (* let args_sorts = List.map (fun v -> type_to_sort v.var_type) args in *)
  if !debug then
    Format.eprintf "Registering fdecl %s (%a)@."
      name
      (Utils.fprintf_list ~sep:"@ "
	 (fun fmt sort -> Format.fprintf fmt "%s" (Z3.Sort.to_string sort)))
      args_sorts
  ;
  let fdecl = Z3.FuncDecl.mk_func_decl_s !ctx name args_sorts bool_sort in
  Z3.Fixedpoint.register_relation !fp fdecl;
  register_fdecl name fdecl;
  fdecl
  


(* Shared variables to describe counter and uid *)

let idx = Corelang.dummy_var_decl "__idx__" Type_predef.type_int
let idx_var = Z3.Expr.mk_const_f !ctx (decl_var idx) 
let uid = Corelang.dummy_var_decl "__uid__" Type_predef.type_int
let uid_fd = Z3.FuncDecl.mk_func_decl_s !ctx "__uid__" [] uid_sort 
let _ = register_fdecl "__uid__"  uid_fd  
let uid_var = Z3.Expr.mk_const_f !ctx uid_fd 

(** Conversion functions

    The following is similar to the Horn backend. Each printing function is
    rephrased from pp_xx to xx_to_expr and produces a Z3 value.

*)


(* Returns the f_decl associated to the variable v *)
let horn_var_to_expr v =
  Z3.Expr.mk_const_f !ctx (get_fdecl v.var_id)




  (* Used to print boolean constants *)
let horn_tag_to_expr t =
  if t = Corelang.tag_true then
    Z3.Boolean.mk_true !ctx
  else if t = Corelang.tag_false then
    Z3.Boolean.mk_false !ctx
  else
    (* Finding the associated sort *)
    let sort = get_tag_sort t in
    let elems = get_sort_elems sort in 
    let res : Z3.Expr.expr option =
      List.fold_left2 (fun res cst expr ->
          match res with
          | Some _ -> res
          | None -> if t = cst then Some (expr:Z3.Expr.expr) else None
        ) None elems (Z3.Enumeration.get_consts sort)
    in
    match res with None -> assert false | Some s -> s
    
(* Prints a constant value *)
let rec horn_const_to_expr c =
  match c with
    | Const_int i    -> Z3.Arithmetic.Integer.mk_numeral_i !ctx i
    | Const_real (_,_,s)   -> Z3.Arithmetic.Real.mk_numeral_i !ctx 0
    | Const_tag t    -> horn_tag_to_expr t
    | _              -> assert false



(* Default value for each type, used when building arrays. Eg integer array
   [2;7] is defined as (store (store (0) 1 7) 0 2) where 0 is this default value
   for the type integer (arrays).
*)
let rec horn_default_val t =
  let t = Types.dynamic_type t in
  if Types.is_bool_type t  then Z3.Boolean.mk_true !ctx else
  if Types.is_int_type t then Z3.Arithmetic.Integer.mk_numeral_i !ctx 0 else 
  if Types.is_real_type t then Z3.Arithmetic.Real.mk_numeral_i !ctx 0 else 
  (* match (Types.dynamic_type t).Types.tdesc with
   * | Types.Tarray(dim, l) -> (\* TODO PL: this strange code has to be (heavily) checked *\)
   *    let valt = Types.array_element_type t in
   *    fprintf fmt "((as const (Array Int %a)) %a)"
   *      pp_type valt 
   *      pp_default_val valt
   * | Types.Tstruct(l) -> assert false
   * | Types.Ttuple(l) -> assert false
   * |_ -> *) assert false

(* Conversion of basic library functions *)
    
let horn_basic_app i val_to_expr vl =
  match i, vl with
  | "ite", [v1; v2; v3] ->
     Z3.Boolean.mk_ite
       !ctx
       (val_to_expr v1)
       (val_to_expr v2)
       (val_to_expr v3)

  | "uminus", [v] ->
     Z3.Arithmetic.mk_unary_minus
       !ctx
       (val_to_expr v)
  | "not", [v] ->
     Z3.Boolean.mk_not
       !ctx
       (val_to_expr v)
  | "=", [v1; v2] ->
     Z3.Boolean.mk_eq
       !ctx
       (val_to_expr v1)
       (val_to_expr v2)
  | "&&", [v1; v2] ->
     Z3.Boolean.mk_and
       !ctx
       [val_to_expr v1;
        val_to_expr v2]
  | "||", [v1; v2] ->
          Z3.Boolean.mk_or
       !ctx
       [val_to_expr v1;
        val_to_expr v2]

  | "impl", [v1; v2] ->
     Z3.Boolean.mk_implies
       !ctx
       (val_to_expr v1)
       (val_to_expr v2)
 | "mod", [v1; v2] ->
          Z3.Arithmetic.Integer.mk_mod
       !ctx
       (val_to_expr v1)
       (val_to_expr v2)
  | "equi", [v1; v2] ->
          Z3.Boolean.mk_eq
       !ctx
       (val_to_expr v1)
       (val_to_expr v2)
  | "xor", [v1; v2] ->
          Z3.Boolean.mk_xor
       !ctx
       (val_to_expr v1)
       (val_to_expr v2)
  | "!=", [v1; v2] ->
     Z3.Boolean.mk_not
       !ctx
       (
         Z3.Boolean.mk_eq
           !ctx
           (val_to_expr v1)
           (val_to_expr v2)
       )
  | "/", [v1; v2] ->
     Z3.Arithmetic.mk_div
       !ctx
       (val_to_expr v1)
       (val_to_expr v2)

  | "+", [v1; v2] ->
     Z3.Arithmetic.mk_add
       !ctx
       [val_to_expr v1; val_to_expr v2]

  | "-", [v1; v2] ->
     Z3.Arithmetic.mk_sub
       !ctx
       [val_to_expr v1 ; val_to_expr v2]
       
  | "*", [v1; v2] ->
     Z3.Arithmetic.mk_mul
       !ctx
       [val_to_expr v1; val_to_expr v2]


  | "<", [v1; v2] ->
     Z3.Arithmetic.mk_lt
       !ctx
       (val_to_expr v1)
       (val_to_expr v2)

  | "<=", [v1; v2] ->
     Z3.Arithmetic.mk_le
       !ctx
       (val_to_expr v1)
       (val_to_expr v2)

  | ">", [v1; v2] ->
     Z3.Arithmetic.mk_gt
       !ctx
       (val_to_expr v1)
       (val_to_expr v2)

  | ">=", [v1; v2] ->
     Z3.Arithmetic.mk_ge
       !ctx
       (val_to_expr v1)
       (val_to_expr v2)


    
  (* | _, [v1; v2] ->      Z3.Boolean.mk_and
   *      !ctx
   *      (val_to_expr v1)
   *      (val_to_expr v2)
   * 
   *      Format.fprintf fmt "(%s %a %a)" i val_to_exprr v1 val_to_expr v2 *)
  | _ -> (
    let msg fmt = Format.fprintf fmt
                    "internal error: zustre unkown function %s (nb args = %i)@."
                    i (List.length vl)
    in
    raise (UnknownFunction(i, msg))
  )

           
(* Convert a value expression [v], with internal function calls only.  [pp_var]
   is a printer for variables (typically [pp_c_var_read]), but an offset suffix
   may be added for array variables
*)
let rec horn_val_to_expr ?(is_lhs=false) m self v =
  match v.value_desc with
  | Cst c       -> horn_const_to_expr c

  (* Code specific for arrays *)
  | Array il    ->
     (* An array definition: 
	(store (
	  ...
 	    (store (
	       store (
	          default_val
	       ) 
	       idx_n val_n
	    ) 
	    idx_n-1 val_n-1)
	  ... 
	  idx_1 val_1
	) *)
     let rec build_array (tab, x) =
       match tab with
       | [] -> horn_default_val v.value_type(* (get_type v) *)
       | h::t ->
	  Z3.Z3Array.mk_store
            !ctx
	    (build_array (t, (x+1)))
	    (Z3.Arithmetic.Integer.mk_numeral_i !ctx x)
	    (horn_val_to_expr ~is_lhs:is_lhs m self h)
     in
     build_array (il, 0)
     
  | Access(tab,index) ->
     Z3.Z3Array.mk_select !ctx 
       (horn_val_to_expr ~is_lhs:is_lhs m self tab)
       (horn_val_to_expr ~is_lhs:is_lhs m self index)

  (* Code specific for arrays *)
    
  | Power (v, n)  -> assert false
  | Var v    ->
     if is_memory m v then
       if Types.is_array_type v.var_type
       then assert false
       else horn_var_to_expr (rename_machine self ((if is_lhs then rename_next else rename_current) (* self *) v))
     
     else 
       horn_var_to_expr
         (rename_machine
            self
            v)
  | Fun (n, vl)   -> horn_basic_app n (horn_val_to_expr m self) vl

let no_reset_to_exprs machines m i =
  let (n,_) = List.assoc i m.minstances in
  let target_machine = List.find (fun m  -> m.mname.node_id = (Corelang.node_name n)) machines in

  let m_list = 
    rename_machine_list
      (concat m.mname.node_id i)
      (rename_mid_list (full_memory_vars machines target_machine))
  in
  let c_list =
    rename_machine_list
      (concat m.mname.node_id i)
      (rename_current_list (full_memory_vars machines target_machine))
  in
  match c_list, m_list with
  | [chd], [mhd] ->
     let expr =
       Z3.Boolean.mk_eq !ctx 
         (horn_var_to_expr mhd)
         (horn_var_to_expr chd)
     in
     [expr]
  | _ -> (
    let exprs =
      List.map2 (fun mhd chd -> 
          Z3.Boolean.mk_eq !ctx 
            (horn_var_to_expr mhd)
            (horn_var_to_expr chd)
        )
        m_list
        c_list
    in
    exprs
  )

let instance_reset_to_exprs machines m i =
  let (n,_) = List.assoc i m.minstances in
  let target_machine = List.find (fun m  -> m.mname.node_id = (Corelang.node_name n)) machines in
  let vars =
    (rename_machine_list
       (concat m.mname.node_id i)
       (rename_current_list (full_memory_vars machines target_machine))@  (rename_mid_list (full_memory_vars machines target_machine))
    )
    
  in
  let expr =
    Z3.Expr.mk_app
      !ctx
      (get_fdecl (machine_reset_name (Corelang.node_name n)))
      (List.map (horn_var_to_expr) (idx::uid::vars))
  in
  [expr]

let instance_call_to_exprs machines reset_instances m i inputs outputs =
  let self = m.mname.node_id in

  (* Building call args *)
  let idx_uid_inout =
    (* Additional input to register step counters, and uid *)
    let idx = horn_var_to_expr idx in
    let uid = uid_conc (get_instance_uid i) (horn_var_to_expr uid) in
    let inout = 
      List.map (horn_val_to_expr m self)
	(inputs @ (List.map (fun v -> mk_val (Var v) v.var_type) outputs))
    in
    idx::uid::inout
  in
    
  try (* stateful node instance *)
    begin
      let (n,_) = List.assoc i m.minstances in
      let target_machine = List.find (fun m  -> m.mname.node_id = Corelang.node_name n) machines in

      (* Checking whether this specific instances has been reset yet *)
      let reset_exprs = 
        if not (List.mem i reset_instances) then
	  (* If not, declare mem_m = mem_c *)
	  no_reset_to_exprs machines m i
        else
          [] (* Nothing to add yet *)
      in
      
      let mems = full_memory_vars machines target_machine in
      let rename_mems f = rename_machine_list (concat m.mname.node_id i) (f mems) in
      let mid_mems = rename_mems rename_mid_list in
      let next_mems = rename_mems rename_next_list in

      let call_expr = 
	match Corelang.node_name n, inputs, outputs, mid_mems, next_mems with
	| "_arrow", [i1; i2], [o], [mem_m], [mem_x] -> begin
          let stmt1 = (* out = ite mem_m then i1 else i2 *)
            Z3.Boolean.mk_eq !ctx
              ( (* output var *)
                horn_val_to_expr 
                  ~is_lhs:true
                  m self
                  (mk_val (Var o) o.var_type)
              )
              (
                Z3.Boolean.mk_ite !ctx 
	          (horn_var_to_expr mem_m) 
	          (horn_val_to_expr m self i1)
	          (horn_val_to_expr m self i2)
              )
          in
          let stmt2 = (* mem_X = false *)
            Z3.Boolean.mk_eq !ctx
	      (horn_var_to_expr mem_x)
              (Z3.Boolean.mk_false !ctx)
          in
          [stmt1; stmt2]
	end

	| node_name_n ->
           let expr = 
             Z3.Expr.mk_app
               !ctx
               (get_fdecl (machine_step_name (node_name n)))
               ( (* Arguments are input, output, mid_mems, next_mems *)
		 idx_uid_inout @ List.map (horn_var_to_expr) (mid_mems@next_mems)
		    
               )
           in
           [expr]
      in

      reset_exprs@call_expr
    end
  with Not_found -> ( (* stateless node instance *)
    let (n,_) = List.assoc i m.mcalls in
    let expr = 
      Z3.Expr.mk_app
        !ctx
        (get_fdecl (machine_stateless_name (node_name n)))
        idx_uid_inout 	  (* Arguments are inputs, outputs *)
    in
    [expr]
  )


    
(* (\* Prints a [value] indexed by the suffix list [loop_vars] *\) *)
(* let rec value_suffix_to_expr self value = *)
(*  match value.value_desc with *)
(*  | Fun (n, vl)  ->  *)
(*     horn_basic_app n (horn_val_to_expr self) (value_suffix_to_expr self vl) *)
    
(*  |  _            -> *)
(*    horn_val_to_expr self value *)


(* type_directed assignment: array vs. statically sized type
   - [var_type]: type of variable to be assigned
   - [var_name]: name of variable to be assigned
   - [value]: assigned value
   - [pp_var]: printer for variables
*)
let assign_to_exprs m var_name value =
  let self = m.mname.node_id in
  let e =
    Z3.Boolean.mk_eq
      !ctx
      (horn_val_to_expr ~is_lhs:true m self var_name)
      (horn_val_to_expr m self value)
  (* was: TODO deal with array accesses       (value_suffix_to_expr self value) *)
  in
  [e]

    
(* Convert instruction to Z3.Expr and update the set of reset instances *)
let rec instr_to_exprs machines reset_instances (m: machine_t) instr : Z3.Expr.expr list * ident list =
  match Corelang.get_instr_desc instr with
  | MComment _ -> [], reset_instances
  | MNoReset i -> (* we assign middle_mem with mem_m. And declare i as reset *)
    no_reset_to_exprs machines m i,
    i::reset_instances
  | MReset i -> (* we assign middle_mem with reset: reset(mem_m) *)
    instance_reset_to_exprs machines m i,
    i::reset_instances
  | MLocalAssign (i,v) ->
    assign_to_exprs
      m  
      (mk_val (Var i) i.var_type) v,
    reset_instances
  | MStateAssign (i,v) ->
    assign_to_exprs
      m 
      (mk_val (Var i) i.var_type) v,
    reset_instances
  | MStep ([i0], i, vl) when Basic_library.is_internal_fun i (List.map (fun v -> v.value_type) vl) ->
    assert false (* This should not happen anymore *)
  | MStep (il, i, vl) ->
    (* if reset instance, just print the call over mem_m , otherwise declare mem_m =
       mem_c and print the call to mem_m *)
    instance_call_to_exprs machines reset_instances m i vl il,
    reset_instances (* Since this instance call will only happen once, we
		       don't have to update reset_instances *)

  | MBranch (g,hl) -> (* (g = tag1 => expr1) and (g = tag2 => expr2) ...
			 should not be produced yet. Later, we will have to
			 compare the reset_instances of each branch and
			 introduced the mem_m = mem_c for branches to do not
			 address it while other did. Am I clear ? *)
    (* For each branch we obtain the logical encoding, and the information
       whether a sub node has been reset or not. If a node has been reset in one
       of the branch, then all others have to have the mem_m = mem_c
       statement. *)
    let self = m.mname.node_id in
    let branch_to_expr (tag, instrs) =
      let branch_def, branch_resets = instrs_to_expr machines reset_instances m instrs in
      let e =
	Z3.Boolean.mk_implies !ctx
          (Z3.Boolean.mk_eq !ctx 
             (horn_val_to_expr m self g)
	     (horn_tag_to_expr tag))
          branch_def in

      [e], branch_resets
	  
    in
    List.fold_left (fun (instrs, resets) b ->
      let b_instrs, b_resets = branch_to_expr b in
      instrs@b_instrs, resets@b_resets 
    ) ([], reset_instances) hl 

and instrs_to_expr machines reset_instances m instrs = 
  let instr_to_exprs rs i = instr_to_exprs machines rs m i in
  let e_list, rs = 
    match instrs with
    | [x] -> instr_to_exprs reset_instances x 
    | _::_ -> (* TODO: check whether we should compuyte a AND on the exprs (expr list) built here. It was performed in the printer setting but seems to be useless here since the output is a list of exprs *)
       
       List.fold_left (fun (exprs, rs) i -> 
         let exprs_i, rs_i = instr_to_exprs rs i in
         exprs@exprs_i, rs@rs_i
       )
         ([], reset_instances) instrs 
	 
	 
    | [] -> [], reset_instances
  in
  let e = 
    match e_list with
    | [e] -> e
    | [] -> Z3.Boolean.mk_true !ctx
    | _ -> Z3.Boolean.mk_and !ctx e_list
  in
  e, rs


(*********************************************************)

(* Quantifiying universally all occuring variables *)
let add_rule ?(dont_touch=[]) vars  expr =
  (* let fds = Z3.Expr.get_args expr in *)
  (* Format.eprintf "Expr %s: args: [%a]@." *)
  (*   (Z3.Expr.to_string expr) *)
  (*   (Utils.fprintf_list ~sep:", " (fun fmt e -> Format.pp_print_string fmt (Z3.Expr.to_string e))) fds; *)

  (* (\* Old code relying on provided vars *\) *)
  (* let sorts = (List.map (fun id -> type_to_sort id.var_type) vars) in *)
  (* let symbols = (List.map (fun id -> Z3.FuncDecl.get_name (get_fdecl id.var_id)) vars) in *)
  
  (* New code: we extract vars from expr *)
  let module FDSet = Set.Make (struct type t = Z3.FuncDecl.func_decl
				      let compare = compare
				      let hash = Hashtbl.hash
  end)
  in
  let rec get_expr_vars e =
    let open Utils in
    let nb_args = Z3.Expr.get_num_args e in
    if nb_args <= 0 then (
      let fdecl = Z3.Expr.get_func_decl e in
      (* let params = Z3.FuncDecl.get_parameters fdecl in *)
      (* Format.eprintf "Extracting info about %s: @." (Z3.Expr.to_string e); *)
      let dkind = Z3.FuncDecl.get_decl_kind fdecl in
      match dkind with Z3enums.OP_UNINTERPRETED -> (
	(* Format.eprintf "kind = %s, " (match dkind with Z3enums.OP_TRUE -> "true" | Z3enums.OP_UNINTERPRETED -> "uninter"); *)
	(* let open Z3.FuncDecl.Parameter in *)
	(* List.iter (fun p -> *)
	(*   match p with *)
        (*     P_Int i -> Format.eprintf "int %i" i *)
	(*   | P_Dbl f -> Format.eprintf "dbl %f" f *)
	(*   | P_Sym s -> Format.eprintf "symb"  *)
	(*   | P_Srt s -> Format.eprintf "sort"  *)
	(*   | P_Ast _ ->Format.eprintf "ast"  *)
	(*   | P_Fdl f -> Format.eprintf "fundecl"  *)
	(*   | P_Rat s -> Format.eprintf "rat %s" s  *)
	     
	(* ) params; *)
	(* Format.eprintf "]@."; *)
	FDSet.singleton fdecl
      )
      | _ -> FDSet.empty
    )
    else (*if nb_args > 0 then*)
      List.fold_left
	(fun accu e ->  FDSet.union accu (get_expr_vars e))
	FDSet.empty (Z3.Expr.get_args e)
  in
  let extracted_vars = FDSet.elements (FDSet.diff (get_expr_vars expr) (FDSet.of_list dont_touch)) in
  let extracted_sorts = List.map Z3.FuncDecl.get_range extracted_vars in
  let extracted_symbols = List.map Z3.FuncDecl.get_name extracted_vars in

  if !debug then (
    Format.eprintf "Declaring rule: %s with variables @[<v 0>@ [%a@ ]@]@ @."
      (Z3.Expr.to_string expr)
      (Utils.fprintf_list ~sep:",@ " (fun fmt e -> Format.fprintf fmt "%s" (Z3.Expr.to_string e))) (List.map horn_var_to_expr vars)
  )
    ;
  let expr = Z3.Quantifier.mk_forall_const
    !ctx  (* context *)
    (List.map horn_var_to_expr vars) (* TODO provide bounded variables as expr *)
    (* sorts           (\* sort list*\) *)
    (* symbols (\* symbol list *\) *)
    expr (* expression *)
    None (* quantifier weight, None means 1 *)
    [] (* pattern list ? *)
    [] (* ? *)
    None (* ? *)
    None (* ? *)
  in
  (* Format.eprintf "OK@.@?"; *)

  (*
    TODO: bizarre la declaration de INIT tout seul semble poser pb.
  *) 
  Z3.Fixedpoint.add_rule !fp
    (Z3.Quantifier.expr_of_quantifier expr)
    None

 
(********************************************************)
    
let machine_reset machines m =
  let locals = local_memory_vars machines m in
  
  (* print "x_m = x_c" for each local memory *)
  let mid_mem_def =
    List.map (fun v ->
      Z3.Boolean.mk_eq !ctx
	(horn_var_to_expr (rename_mid v))
	(horn_var_to_expr (rename_current v))
    ) locals
  in

  (* print "child_reset ( associated vars _ {c,m} )" for each subnode.
     Special treatment for _arrow: _first = true
  *)

  let reset_instances =
    
    List.map (fun (id, (n, _)) ->
      let name = node_name n in
      if name = "_arrow" then (
	Z3.Boolean.mk_eq !ctx
	  (
	    let vdecl = get_fdecl ((concat m.mname.node_id id) ^ "._arrow._first_m") in
	    Z3.Expr.mk_const_f !ctx vdecl
	  )
	  (Z3.Boolean.mk_true !ctx)
	  
      ) else (
	let machine_n = get_machine machines name in 
	
	Z3.Expr.mk_app
	  !ctx
	  (get_fdecl (name ^ "_reset"))
	  (List.map (horn_var_to_expr)
	     (idx::uid:: (* Additional vars: counters, uid *)
	      	(rename_machine_list (concat m.mname.node_id id) (reset_vars machines machine_n))
	  ))
	  
      )
    ) m.minstances
      
      
  in
  
  Z3.Boolean.mk_and !ctx (mid_mem_def @ reset_instances)
    
        

(*  TODO: empty list means true statement *)
let decl_machine machines m =
  if m.mname.node_id = Arrow.arrow_id then
    (* We don't do arrow function *)
    ()
  else
    begin
      let _ =
        List.map decl_var
      	  (
      	    (inout_vars machines m)@
      	      (rename_current_list (full_memory_vars machines m)) @
      	      (rename_mid_list (full_memory_vars machines m)) @
      	      (rename_next_list (full_memory_vars machines m)) @
      	      (rename_machine_list m.mname.node_id m.mstep.step_locals)
      	  )
      in
      if is_stateless m then
	begin
	  if !debug then 
	    Format.eprintf "Declaring a stateless machine: %s@." m.mname.node_id;

	  (* Declaring single predicate *)
	  let vars = inout_vars machines m in
	  let vars_types = List.map (fun v -> type_to_sort v.var_type) vars in
	  let _ = decl_rel (machine_stateless_name m.mname.node_id) vars_types in
	  
	  let horn_body, _ (* don't care for reset here *) =
	    instrs_to_expr
	      machines
	      ([] (* No reset info for stateless nodes *) )
	      m
	      m.mstep.step_instrs
	  in
	  let horn_head = 
	    Z3.Expr.mk_app
	      !ctx
	      (get_fdecl (machine_stateless_name m.mname.node_id))
	      (	List.map (horn_var_to_expr) (idx::uid:: (* Additional vars: counters, uid *) vars))
	  in
	  (* this line seems useless *)
	  let vars = idx::uid::vars@(rename_machine_list m.mname.node_id m.mstep.step_locals) in
	  (* Format.eprintf "useless Vars: %a@." (Utils.fprintf_list ~sep:"@ " Printers.pp_var) vars; *)
	  match m.mstep.step_asserts with
	  | [] ->
	     begin
	       (* Rule for single predicate : "; Stateless step rule @." *)
	       (*let vars = rename_machine_list m.mname.node_id m.mstep.step_locals in*)
	       (* TODO clean code *)
	       (* Format.eprintf "used Vars: %a@." (Utils.fprintf_list ~sep:"@ " Printers.pp_var) vars; *)
	       add_rule vars (Z3.Boolean.mk_implies !ctx horn_body horn_head)
		 
	     end
	  | assertsl ->
	     begin
	       (*Rule for step "; Stateless step rule with Assertions @.";*)
	       let body_with_asserts =
		 Z3.Boolean.mk_and !ctx (horn_body :: List.map (horn_val_to_expr m m.mname.node_id) assertsl)
	       in
	       let vars = rename_machine_list m.mname.node_id m.mstep.step_locals in
	       add_rule vars (Z3.Boolean.mk_implies !ctx body_with_asserts horn_head)
	     end
	end
      else
	begin

	  (* Rule for reset *)

	  let vars = reset_vars machines m in
	  let vars_types = List.map (fun v -> type_to_sort v.var_type) vars in
	  let _ = decl_rel (machine_reset_name m.mname.node_id) vars_types in
	  let horn_reset_body = machine_reset machines m in	    
	  let horn_reset_head = 
	    Z3.Expr.mk_app
	      !ctx
	      (get_fdecl (machine_reset_name m.mname.node_id))
	      (	List.map (horn_var_to_expr) (idx::uid:: (* Additional vars: counters, uid *) vars))
	  in

	  
	  let _ =
	    add_rule (idx::uid::vars) (Z3.Boolean.mk_implies !ctx horn_reset_body horn_reset_head)
	      
	  in

	  (* Rule for step*)
	  let vars = step_vars machines m in
  	  let vars_types = List.map (fun v -> type_to_sort v.var_type) vars in
          let _ = decl_rel (machine_step_name m.mname.node_id) vars_types in
	  let horn_step_body, _ (* don't care for reset here *) =
	    instrs_to_expr
	      machines
	      []
	      m
	      m.mstep.step_instrs
	  in
	  let horn_step_head = 
	    Z3.Expr.mk_app
	      !ctx
	      (get_fdecl (machine_step_name m.mname.node_id))
	      (	List.map (horn_var_to_expr) (idx::uid:: (* Additional vars: counters, uid *) vars))
	  in
	  match m.mstep.step_asserts with
	  | [] ->
	     begin
	       (* Rule for single predicate *) 
	       let vars = (step_vars_c_m_x machines m) @(rename_machine_list m.mname.node_id m.mstep.step_locals) in
	       add_rule (idx::uid::vars) (Z3.Boolean.mk_implies !ctx horn_step_body horn_step_head)
		 
	     end
	  | assertsl ->
	     begin
	       (* Rule for step Assertions @.; *)
	       let body_with_asserts =
		 Z3.Boolean.mk_and !ctx
		   (horn_step_body :: List.map (horn_val_to_expr m m.mname.node_id) assertsl)
	       in
	       let vars = (step_vars_c_m_x machines m) @(rename_machine_list m.mname.node_id m.mstep.step_locals) in
	       add_rule (idx::uid::vars) (Z3.Boolean.mk_implies !ctx body_with_asserts horn_step_head)
		 
	     end
     	       
	end
    end



(* Debug functions *)

let rec extract_expr_fds e =
  (* Format.eprintf "@[<v 2>Extracting fundecls from expr %s@ " *)
  (*   (Z3.Expr.to_string e); *)
  
  (* Removing quantifier is there are some *)
  let e = (* I didn't found a nicer way to do it than with an exception.  My
	     bad *)
    try
      let eq = Z3.Quantifier.quantifier_of_expr e in
      let e2 = Z3.Quantifier.get_body eq in
      (* Format.eprintf "Extracted quantifier body@ "; *)
      e2
	
    with _ -> Format.eprintf "No quantifier info@ "; e
  in
  let _ =
    try 
    (
      let fd = Z3.Expr.get_func_decl e in
      let fd_symbol = Z3.FuncDecl.get_name fd in
      let fd_name = Z3.Symbol.to_string fd_symbol in
      if not (Hashtbl.mem decls fd_name) then
	register_fdecl fd_name fd;
      (* Format.eprintf "fdecls (%s): %s@ " *)
      (* 	fd_name *)
      (* 	(Z3.FuncDecl.to_string fd); *)
      try
	(
	  let args = Z3.Expr.get_args e in
	  (* Format.eprintf "@[<v>@ "; *)
	  (* List.iter extract_expr_fds args; *)
	  (* Format.eprintf "@]@ "; *)
	  ()
	)
      with _ ->
	Format.eprintf "Impossible to extract fundecl args for expression %s@ "
	  (Z3.Expr.to_string e)
    )
  with _ ->
    Format.eprintf "Impossible to extract anything from expression %s@ "
      (Z3.Expr.to_string e)
  in
  (* Format.eprintf "@]@ " *)
  ()      

(* Local Variables: *)
(* compile-command:"make -C ../.." *)
(* End: *)
