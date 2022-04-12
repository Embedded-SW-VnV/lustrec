val bool_sort: Z3.Sort.sort
val horn_const_to_expr : Lustre_types.constant -> Z3.Expr.expr
val horn_tag_to_expr : Lustre_types.label -> Z3.Expr.expr
val get_fdecl: Utils.ident -> Z3.FuncDecl.func_decl
val horn_basic_app: Utils.ident -> Z3.Expr.expr list -> Types.t list * Types.t -> Z3.Expr.expr
val decl_sorts: unit -> unit
val type_to_sort: Types.t -> Z3.Sort.sort
val register_fdecl: Utils.ident -> Z3.FuncDecl.func_decl -> unit
val uid_sort: Z3.Sort.sort
val int_sort: Z3.Sort.sort

val full_memory_vars: ?without_arrow:bool -> Machine_code_types.machine_t list -> Machine_code_types.machine_t -> Lustre_types.var_decl list

val rename_machine_list : Utils.ident -> Lustre_types.var_decl list -> Lustre_types.var_decl list
val rename_next_list : Lustre_types.var_decl list -> Lustre_types.var_decl list
val rename_current_list : Lustre_types.var_decl list -> Lustre_types.var_decl list

exception UnknownFunction of (string * (Format.formatter -> unit))
                                                                                                                   
val decl_rel: ?no_additional_vars: bool -> Utils.ident (*  name *) -> Z3.Sort.sort list (* args_sorts *) -> Z3.FuncDecl.func_decl
val preprocess: Machine_code_types.machine_t list ->
                Machine_code_types.machine_t list 

val decl_machine: Machine_code_types.machine_t list -> Machine_code_types.machine_t -> unit
val decl_var: Lustre_types.var_decl -> Z3.FuncDecl.func_decl

val horn_var_to_expr: Lustre_types.var_decl -> Z3.Expr.expr
val step_vars_m_x : Machine_code_types.machine_t list -> Machine_code_types.machine_t -> Lustre_types.var_decl list
val step_vars_c_m_x : Machine_code_types.machine_t list -> Machine_code_types.machine_t -> Lustre_types.var_decl list
val machine_reset_name: Utils.ident -> Utils.ident
  
val machine_step_name: Utils.ident -> Utils.ident
(*val pp_machine_stateless_name : Format.formatter -> Utils.ident -> unit*)
val machine_stateless_name: Utils.ident -> Utils.ident

val add_rule: ?dont_touch: 'a list -> Lustre_types.var_decl list -> Z3.Expr.expr -> unit
val reset_vars : Machine_code_types.machine_t list -> Machine_code_types.machine_t -> Lustre_types.var_decl list
val step_vars : Machine_code_types.machine_t list -> Machine_code_types.machine_t -> Lustre_types.var_decl list
