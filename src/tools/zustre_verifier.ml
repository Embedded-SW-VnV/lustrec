open LustreSpec
open Machine_code
open Format
(* open Horn_backend_common
 * open Horn_backend *)

module HBC = Horn_backend_common
let machine_step_name = HBC.machine_step_name
let node_name = HBC.node_name
let concat = HBC.concat
let rename_machine = HBC.rename_machine
let rename_machine_list = HBC.rename_machine_list
let rename_next = HBC.rename_next
let rename_current = HBC.rename_current
let rename_current_list = HBC.rename_current_list
let rename_mid_list = HBC.rename_mid_list
let rename_next_list = HBC.rename_next_list
let full_memory_vars = HBC.full_memory_vars
   
let active = ref false
let ctx = ref (Z3.mk_context [])
let machine_reset_name = HBC.machine_reset_name 
let machine_stateless_name = HBC.machine_stateless_name 

(** Sorts

A sort is introduced for each basic type and each enumerated type.

A hashtbl records these and allow easy access to sort values, when
   provided with a enumerated type name. 

*)
        
let bool_sort = Z3.Boolean.mk_sort !ctx
let int_sort = Z3.Arithmetic.Integer.mk_sort !ctx
let real_sort = Z3.Arithmetic.Real.mk_sort !ctx

let const_sorts = Hashtbl.create 13
let const_tags = Hashtbl.create 13
let sort_elems = Hashtbl.create 13

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
          
	| _ -> assert false
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

(** Func decls

Similarly fun_decls are registerd, by their name, into a hashtbl. The
   proposed encoding introduces a 0-ary fun_decl to model variables
   and fun_decl with arguments to declare reset and step predicates.



 *)
let decls = Hashtbl.create 13
let register_fdecl id fd = Hashtbl.add decls id fd
let get_fdecl id = Hashtbl.find decls id
                 
let decl_var id =
  let fdecl = Z3.FuncDecl.mk_func_decl_s !ctx id.var_id [] (type_to_sort id.var_type) in
  register_fdecl id.var_id fdecl;
  fdecl

let decl_rel name args =
  (*verifier ce qui est construit. On veut un declare-rel *)
  let args_sorts = List.map (fun v -> type_to_sort v.var_type) args in
  let fdecl = Z3.FuncDecl.mk_func_decl_s !ctx name args_sorts bool_sort in
  register_fdecl name fdecl;
  fdecl
  


(** conversion functions

The following is similar to the Horn backend. Each printing function
   is rephrased from pp_xx to xx_to_expr and produces a Z3 value.

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

  (* | _, [v1; v2] ->      Z3.Boolean.mk_and
   *      !ctx
   *      (val_to_expr v1)
   *      (val_to_expr v2)
   * 
   *      Format.fprintf fmt "(%s %a %a)" i val_to_exprr v1 val_to_expr v2 *)
  | _ -> (
    Format.eprintf
      "internal error: zustre unkown function %s@." i;
    assert false)

           
(* Convert a value expression [v], with internal function calls only.
   [pp_var] is a printer for variables (typically [pp_c_var_read]),
   but an offset suffix may be added for array variables
*)
let rec horn_val_to_expr ?(is_lhs=false) self v =
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
	    (horn_val_to_expr ~is_lhs:is_lhs self h)
     in
     build_array (il, 0)
       
  | Access(tab,index) ->
     Z3.Z3Array.mk_select !ctx 
       (horn_val_to_expr ~is_lhs:is_lhs self tab)
       (horn_val_to_expr ~is_lhs:is_lhs self index)

  (* Code specific for arrays *)
    
  | Power (v, n)  -> assert false
  | LocalVar v    ->
     horn_var_to_expr
       (rename_machine
          self
          v)
  | StateVar v    ->
     if Types.is_array_type v.var_type
     then assert false
     else horn_var_to_expr (rename_machine self ((if is_lhs then rename_next else rename_current) (* self *) v))
  | Fun (n, vl)   -> horn_basic_app n (horn_val_to_expr self) vl

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
    (
      (rename_machine_list
	 (concat m.mname.node_id i)
	 (rename_current_list (full_memory_vars machines target_machine))
      ) 
      @
	(rename_machine_list
	   (concat m.mname.node_id i)
	   (rename_mid_list (full_memory_vars machines target_machine))
	)
    )
  in
  let expr =
    Z3.Expr.mk_app
      !ctx
      (get_fdecl (machine_reset_name (Corelang.node_name n)))
      (List.map (horn_var_to_expr) vars)
  in
  [expr]

let instance_call_to_exprs machines reset_instances m i inputs outputs =
  let self = m.mname.node_id in
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
                  self
                  (mk_val (LocalVar o) o.var_type)
              )
              (
                Z3.Boolean.mk_ite !ctx 
	          (horn_var_to_expr mem_m) 
	          (horn_val_to_expr self i1)
	          (horn_val_to_expr self i2)
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
               (
                 List.map (horn_val_to_expr self) (
                     inputs @
	               (List.map (fun v -> mk_val (LocalVar v) v.var_type) outputs)
                   )
               ) @ (
                 List.map (horn_var_to_expr) (mid_mems@next_mems)
	       )
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
        ((* Arguments are inputs, outputs *)
         List.map (horn_val_to_expr self)
           (
             inputs @ (List.map (fun v -> mk_val (LocalVar v) v.var_type) outputs)
           )
        )
    in
    [expr]
  )
    

(* Convert instruction to Z3.Expr and update the set of reset instances *)
let rec instr_to_expr machines reset_instances (m: machine_t) instr : Z3.Expr.expr list * ident list =
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
      m (horn_var_to_expr) 
      (mk_val (LocalVar i) i.var_type) v,
    reset_instances
  | MStateAssign (i,v) ->
    assign_to_exprs
      m (horn_var_to_expr) 
      (mk_val (StateVar i) i.var_type) v,
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
      Z3.Boolean.mk_implies
        (Z3.Boolean.mk_eq !ctx 
           (horn_val_to_expr self g)
	   (horn_tag_to_expr tag))
        (machine_instrs_to_exprs machines reset_instances m instrs)
    in
    List.map branch_to_expr hl,
    reset_instances 

and instrs_to_expr machines reset_instances m instrs = 
  let instr_to_expr rs i = instr_to_expr machines rs m i in
  match instrs with
  | [x] -> instr_to_expres reset_instances x 
  | _::_ -> (* TODO: check whether we should compuyte a AND on the exprs (expr list) built here. It was performed in the printer setting but seems to be useless here since the output is a list of exprs *)

      List.fold_left (fun (exprs, rs) i -> 
          let exprs_i, rs = ppi rs i in
          expr@exprs_i, rs
        )
        ([], reset_instances) instrs 
    
    
  | [] -> [], reset_instances


let basic_library_to_horn_expr i vl =
  match i, vl with
  | "ite", [v1; v2; v3] -> Format.fprintf fmt "(@[<hov 2>ite %a@ %a@ %a@])" pp_val v1 pp_val v2 pp_val v3

  | "uminus", [v] -> Format.fprintf fmt "(- %a)" pp_val v
  | "not", [v] -> Format.fprintf fmt "(not %a)" pp_val v
  | "=", [v1; v2] -> Format.fprintf fmt "(= %a %a)" pp_val v1 pp_val v2
  | "&&", [v1; v2] -> Format.fprintf fmt "(and %a %a)" pp_val v1 pp_val v2
  | "||", [v1; v2] -> Format.fprintf fmt "(or %a %a)" pp_val v1 pp_val v2
  | "impl", [v1; v2] -> Format.fprintf fmt "(=> %a %a)" pp_val v1 pp_val v2
  | "mod", [v1; v2] -> Format.fprintf fmt "(mod %a %a)" pp_val v1 pp_val v2
  | "equi", [v1; v2] -> Format.fprintf fmt "(%a = %a)" pp_val v1 pp_val v2
  | "xor", [v1; v2] -> Format.fprintf fmt "(%a xor %a)" pp_val v1 pp_val v2
  | "!=", [v1; v2] -> Format.fprintf fmt "(not (= %a %a))" pp_val v1 pp_val v2
  | "/", [v1; v2] -> Format.fprintf fmt "(div %a %a)" pp_val v1 pp_val v2
  | _, [v1; v2] -> Format.fprintf fmt "(%s %a %a)" i pp_val v1 pp_val v2
  | _ -> (Format.eprintf "internal error: Basic_library.pp_horn %s@." i; assert false)
(*  | "mod", [v1; v2] -> Format.fprintf fmt "(%a %% %a)" pp_val v1 pp_val v2

*)

        
(* Prints a [value] indexed by the suffix list [loop_vars] *)
let rec value_suffix_to_expr self value =
 match value.value_desc with
 | Fun (n, vl)  -> 
   basic_library_to_horn_expr n (value_suffix_to_expr self vl)
 |  _            ->
   horn_val_to_expr self value

        
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
      (horn_val_to_expr ~is_lhs:true self var_name)
      (value_suffix_to_expr self value)
  in
  [e]

(*                TODO: empty list means true statement *)
let decl_machine machines m =
  if m.Machine_code.mname.node_id = Machine_code.arrow_id then
    (* We don't print arrow function *)
    ()
  else
    begin
      let vars =
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
	  (* Declaring single predicate *)
	  let _ = decl_rel (machine_stateless_name m.mname.node_id) (inout_vars machines m) in          
          match m.mstep.step_asserts with
	  | [] ->
	     begin

	       (* Rule for single predicate *)
	       fprintf fmt "; Stateless step rule @.";
	       fprintf fmt "@[<v 2>(rule (=> @ ";
	       ignore (pp_machine_instrs machines ([] (* No reset info for stateless nodes *) )  m fmt m.mstep.step_instrs);
	       fprintf fmt "@ (%a @[<v 0>%a)@]@]@.))@.@."
		 pp_machine_stateless_name m.mname.node_id
		 (Utils.fprintf_list ~sep:" " (horn_var_to_expr)) (inout_vars machines m);
	     end
	  | assertsl ->
	     begin
	       let pp_val = pp_horn_val ~is_lhs:true m.mname.node_id (horn_var_to_expr) in
	       
	       fprintf fmt "; Stateless step rule with Assertions @.";
	       (*Rule for step*)
	       fprintf fmt "@[<v 2>(rule (=> @ (and @ ";
	       ignore (pp_machine_instrs machines [] m fmt m.mstep.step_instrs);
	       fprintf fmt "@. %a)@ (%a @[<v 0>%a)@]@]@.))@.@." (pp_conj pp_val) assertsl
		 pp_machine_stateless_name m.mname.node_id
		 (Utils.fprintf_list ~sep:" " (horn_var_to_expr)) (step_vars machines m);
	  
	     end
	       
	end
      else
	begin
	  (* Declaring predicate *)
	  let _ = decl_rel (machine_reset_name m.mname.node_id) (reset_vars machines m) in
          let _ = decl_rel (machine_step_name m.mname.node_id) (step_vars machines m) in

	  (* Rule for reset *)
	  fprintf fmt "@[<v 2>(rule (=> @ %a@ (%a @[<v 0>%a)@]@]@.))@.@."
	    (pp_machine_reset machines) m 
	    pp_machine_reset_name m.mname.node_id
	    (Utils.fprintf_list ~sep:"@ " (horn_var_to_expr)) (reset_vars machines m);

          match m.mstep.step_asserts with
	  | [] ->
	     begin
	       fprintf fmt "; Step rule @.";
	       (* Rule for step*)
	       fprintf fmt "@[<v 2>(rule (=> @ ";
	       ignore (pp_machine_instrs machines [] m fmt m.mstep.step_instrs);
	       fprintf fmt "@ (%a @[<v 0>%a)@]@]@.))@.@."
		 pp_machine_step_name m.mname.node_id
		 (Utils.fprintf_list ~sep:"@ " (horn_var_to_expr)) (step_vars machines m);
	     end
	  | assertsl -> 
	     begin
	       let pp_val = pp_horn_val ~is_lhs:true m.mname.node_id (horn_var_to_expr) in
	       (* print_string pp_val; *)
	       fprintf fmt "; Step rule with Assertions @.";
	       
	       (*Rule for step*)
	       fprintf fmt "@[<v 2>(rule (=> @ (and @ ";
	       ignore (pp_machine_instrs machines [] m fmt m.mstep.step_instrs);
	       fprintf fmt "@. %a)@ (%a @[<v 0>%a)@]@]@.))@.@." (pp_conj pp_val) assertsl
		 pp_machine_step_name m.mname.node_id
		 (Utils.fprintf_list ~sep:" " (horn_var_to_expr)) (step_vars machines m);
	     end
	       
     	       
	end
    end

let param_stat = ref false
let param_eldarica = ref false
let param_utvpi = ref false
let param_tosmt = ref false
let param_pp = ref false
             
module Verifier =
  (struct
    include VerifierType.Default
    let name = "zustre"
    let options = [
        "-stat", Arg.Set param_stat, "print statistics";
        "-eldarica", Arg.Set param_eldarica, "deactivate fixedpoint extensions when printing rules";
        "-no_utvpi", Arg.Set param_utvpi, "Deactivate UTVPI strategy";
        "-tosmt", Arg.Set param_tosmt, "Print low-level (possibly unreadable) SMT2 statements";
        "-no-pp", Arg.Set param_pp, "No preprocessing (inlining and slicing)";
      ]
                
    let activate () = (
        active := true;
        Options.output := "horn";
      )
    let is_active () = !active

    let get_normalization_params () =
      (* make sure the output is "Horn" *)
      assert(!Options.output = "horn");
      Backends.get_normalization_params ()

    let setup_solver () =
      let fp = Z3.Fixedpoint.mk_fixedpoint !ctx in
      (* let help = Z3.Fixedpoint.get_help fp in
       * Format.eprintf "Fp help : %s@." help;
       * 
       * let solver =Z3.Solver.mk_solver !ctx None in
       * let help = Z3.Solver.get_help solver in
       * Format.eprintf "Z3 help : %s@." help; *)
      
      let module P = Z3.Params in
      let module S = Z3.Symbol in
      let mks = S.mk_string !ctx in
      let params = P.mk_params !ctx in

      (* self.fp.set (engine='spacer') *)
      P.add_symbol params (mks "engine") (mks "spacer");
      
       (* #z3.set_option(rational_to_decimal=True) *)
       (* #self.fp.set('precision',30) *)
      if !param_stat then 
        (* self.fp.set('print_statistics',True) *)
        P.add_bool params (mks "print_statistics") true;

      (* Dont know where to find this parameter *)
      (* if !param_spacer_verbose then
         *   if self.args.spacer_verbose: 
         *        z3.set_option (verbose=1) *)

      (* The option is not recogined*)
      (* self.fp.set('use_heavy_mev',True) *)
      (* P.add_bool params (mks "use_heavy_mev") true; *)
      
      (* self.fp.set('pdr.flexible_trace',True) *)
      P.add_bool params (mks "pdr.flexible_trace") true;

      (* self.fp.set('reset_obligation_queue',False) *)
      P.add_bool params (mks "spacer.reset_obligation_queue") false;

      (* self.fp.set('spacer.elim_aux',False) *)
      P.add_bool params (mks "spacer.elim_aux") false;

      (* if self.args.eldarica:
        *     self.fp.set('print_fixedpoint_extensions', False) *)
      if !param_eldarica then
        P.add_bool params (mks "print_fixedpoint_extensions") false;
      
      (* if self.args.utvpi: self.fp.set('pdr.utvpi', False) *)
      if !param_utvpi then
        P.add_bool params (mks "pdr.utvpi") false;

      (* if self.args.tosmt:
       *        self.log.info("Setting low level printing")
       *        self.fp.set ('print.low_level_smt2',True) *)
      if !param_tosmt then
        P.add_bool params (mks "print.low_level_smt2") true;

      (* if not self.args.pp:
       *        self.log.info("No pre-processing")
       *        self.fp.set ('xform.slice', False)
       *        self.fp.set ('xform.inline_linear',False)
       *        self.fp.set ('xform.inline_eager',False) *\) *)
      if !param_pp then (
        P.add_bool params (mks "xform.slice") false;
        P.add_bool params (mks "xform.inline_linear") false;
        P.add_bool params (mks "xform.inline_eager") false
      );
      Z3.Fixedpoint.set_parameters fp params
        
      
    let run basename prog machines =
      let machines = Machine_code.arrow_machine::machines in
      let machines = preprocess machines in
      setup_solver ();
      decl_sorts ();
      List.iter (decl_machine machines) (List.rev machines);

      
      ()

  end: VerifierType.S)
    
