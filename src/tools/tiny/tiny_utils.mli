val report: ?verbose_level:int ->
           level:int -> (Format.formatter -> unit) -> unit

val machine_to_env : Machine_code_types.machine_t -> Tiny.Ast.Var.Set.t
val  machine_to_ast: (string * ((Q.t * string) * (Q.t * string))) list -> Machine_code_types.machine_t -> Tiny.Ast.stm
                                                                   
