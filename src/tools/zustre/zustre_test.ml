(* Example of a use of Z3 Fixedpoint that doesn't work 
   The file is self-contained and shall be compiled as follow:

   in File _tags, add the simple line
   <**/*>: package(z3)

   Then compile as
   ocamlbuild -use-ocamlfind zustre_test.native

   We obtain the following output:
   $ ./zustre_test.native 
   Registered rules:
     Rule: (forall ((x Int) (y Int)) (=> (= x y) (f x y)))  
     Rule: INIT_STATE
     Rule: (forall ((x Int) (y Int)) (=> (and (f x y) INIT_STATE) (MAIN x y)))
     Rule: (forall ((x Int) (y Int)) (=> (and (not (= x y)) (MAIN x y)) ERR))
     
   Fatal error: exception Z3.Error("Uninterpreted 'y' in <null>:
   f(#0,#1) :- 
     (= (:var 1) y),
     (= (:var 0) x),
     (= x y).
   ")

*)



let rec fprintf_list ~sep:sep f fmt = function
  | []   -> ()
  | [e]  -> f fmt e
  | x::r -> Format.fprintf fmt "%a%(%)%a" f x sep (fprintf_list ~sep f) r

(* Global references to declare Z3 context and Fixedpoint engine *)
     
let ctx = ref (Z3.mk_context [])
let fp = ref (Z3.Fixedpoint.mk_fixedpoint !ctx)

(* Shortcuts to basic sorts *)

let bool_sort = Z3.Boolean.mk_sort !ctx
let int_sort = Z3.Arithmetic.Integer.mk_sort !ctx
let real_sort = Z3.Arithmetic.Real.mk_sort !ctx

  
let _ =


  (* Setting up the fixed point engine *)
  fp := Z3.Fixedpoint.mk_fixedpoint !ctx;
  let module P = Z3.Params in
  let module S = Z3.Symbol in
  let mks = S.mk_string !ctx in
  let params = P.mk_params !ctx in
  P.add_symbol params (mks "engine") (mks "spacer");
  Z3.Fixedpoint.set_parameters !fp params;

  (* Three rules 
     R1: (x = y) => f(x,y)
     R2: INIT and f(x,y) => MAIN(x,y)
     R3: x!=y and MAIN(x,y) => ERR(x,y)
     INIT is assumed as the beginning

     Querying ERR shall be unsat since the only valid MAIN(x,y) are x=y and
     therefore ERR is unsat.
  *)
  
  (* Simple rule : forall x, y, (x=y => f(x,y)) *)
  let x = Z3.FuncDecl.mk_func_decl_s !ctx "x" [] int_sort in
  let y = Z3.FuncDecl.mk_func_decl_s !ctx "y" [] int_sort in
  let x_expr = Z3.Expr.mk_const_f !ctx x in
  let y_expr = Z3.Expr.mk_const_f !ctx y in
  
  let decl_f = Z3.FuncDecl.mk_func_decl_s !ctx "f" [int_sort; int_sort] bool_sort in
  Z3.Fixedpoint.register_relation !fp decl_f; (* since f appears in the rhs of a rule *)
  let f_x_y_expr = Z3.Expr.mk_app !ctx decl_f [x_expr; y_expr] in
  let x_eq_y_expr = Z3.Boolean.mk_eq !ctx x_expr y_expr in
  
  let expr_f_lhs = (* x = y *)
    x_eq_y_expr 
  in
  let expr_f_rhs = f_x_y_expr in
  let expr_f = Z3.Boolean.mk_implies !ctx expr_f_lhs expr_f_rhs in
  (* Adding forall as prefix *)
  let expr_forall_f = Z3.Quantifier.mk_forall_const
    !ctx  (* context *)
    (* [int_sort; int_sort]           (\* sort list*\) *)
    (* [Z3.FuncDecl.get_name x; Z3.FuncDecl.get_name y] (\* symbol list *\) *)
(*    [x_expr; y_expr] Second try with expr list "const" *)
    [Z3.Expr.mk_const_f !ctx x; Z3.Expr.mk_const_f !ctx y]
    expr_f (* expression *)
    None (* quantifier weight, None means 1 *)
    [] (* pattern list ? *)
    [] (* ? *)
    None (* ? *)
    None (* ? *)
  in
  let expr_forall_f = Z3.Quantifier.expr_of_quantifier expr_forall_f in
  Z3.Fixedpoint.add_rule !fp expr_forall_f None;
  
  
  (* INIT RULE *)
  let decl_init = Z3.FuncDecl.mk_func_decl_s !ctx "INIT_STATE" [] bool_sort in
  Z3.Fixedpoint.register_relation !fp decl_init; 
  let init_expr = Z3.Expr.mk_app !ctx decl_init [] in
  Z3.Fixedpoint.add_rule !fp init_expr None;

  (* MAIN is defined by two rules : INIT and induction *)
  let decl_main = Z3.FuncDecl.mk_func_decl_s !ctx "MAIN" [int_sort; int_sort] bool_sort in
  Z3.Fixedpoint.register_relation !fp decl_main;
  let main_x_y_expr = Z3.Expr.mk_app !ctx decl_main [x_expr; y_expr] in
  
  (* Rule 1: forall x, y, INIT_STATE and f(x,y) => MAIN(x,y) : at the beginning x=y *)
  let expr_main1_lhs = (* INIT_STATE and f(x, y) *)
    Z3.Boolean.mk_and !ctx [f_x_y_expr; init_expr] in
  let expr_main1_rhs = main_x_y_expr in
  let expr_main1 = Z3.Boolean.mk_implies !ctx expr_main1_lhs expr_main1_rhs in
  (* Adding forall as prefix *)
  let expr_forall_main1 = Z3.Quantifier.mk_forall_const
    !ctx  (* context *)
    (*
    [int_sort; int_sort]           (* sort list*)
    [Z3.FuncDecl.get_name x; Z3.FuncDecl.get_name y] (* symbol list *)
    *)
    (*    [x_expr; y_expr] Second try with expr list "const" *)
    [Z3.Expr.mk_const_f !ctx x; Z3.Expr.mk_const_f !ctx y]
    expr_main1 (* expression *)
    None (* quantifier weight, None means 1 *)
    [] (* pattern list ? *)
    [] (* ? *)
    None (* ? *)
    None (* ? *)
  in
  let expr_forall_main1 = Z3.Quantifier.expr_of_quantifier expr_forall_main1 in
  Z3.Fixedpoint.add_rule !fp expr_forall_main1 None;

  (* Rule 2: forall x,y, MAIN(x,y) => MAIN(x+1, y+1) *)
  
  
  (* TODO: not implemented yet since the error is visible without it *)
  
  (* Query: is it possible to have MAIN(x,y) and x!=y ? *)
  (* This is performed as follow:
     rule (forall x, y, MAIN(x,y) and x!=y => ERR)
  *)
  let decl_err = Z3.FuncDecl.mk_func_decl_s !ctx "ERR" [] bool_sort in
  Z3.Fixedpoint.register_relation !fp decl_err; 
  let err_expr = Z3.Expr.mk_app !ctx decl_err [] in
  let x_diff_y_expr = Z3.Boolean.mk_not !ctx x_eq_y_expr in
  let expr_err_lhs =
    Z3.Boolean.mk_and !ctx [x_diff_y_expr; main_x_y_expr] in
  let expr_err_rhs = err_expr in
  let expr_err = Z3.Boolean.mk_implies !ctx expr_err_lhs expr_err_rhs in
  (* Adding forall as prefix *)
  let expr_forall_err = Z3.Quantifier.mk_forall_const
    !ctx  (* context *)
(*    [int_sort; int_sort]           (* sort list*)
    [Z3.FuncDecl.get_name x; Z3.FuncDecl.get_name y] (* symbol list *)
*)
    (* [x_expr; y_expr] Second try with expr list "const" *)
    [Z3.Expr.mk_const_f !ctx x; Z3.Expr.mk_const_f !ctx y]
    expr_err (* expression *)
    None (* quantifier weight, None means 1 *)   
    [] (* pattern list ? *)
    [] (* ? *)
    None (* ? *)
    None (* ? *)
  in
  let expr_forall_err = Z3.Quantifier.expr_of_quantifier expr_forall_err in
  Z3.Fixedpoint.add_rule !fp expr_forall_err None;

  (* Printing the rules for sanity check *)
  
  let rules_expr = Z3.Fixedpoint.get_rules !fp in
  Format.eprintf "@[<v 2>Registered rules:@ %a@ @]@."
    (fprintf_list ~sep:"@ "
       (fun fmt e ->
	 (* let e2 = Z3.Quantifier.get_body eq in *)
	 (* let fd = Z3.Expr.get_func_decl e in *)
	 Format.fprintf fmt "Rule: %s@ "
	   (Z3.Expr.to_string e);
       )) rules_expr;


  let res_status = Z3.Fixedpoint.query_r !fp [decl_err] in

  Format.eprintf "Status: %s@." (Z3.Solver.string_of_status res_status)
    
	


  
