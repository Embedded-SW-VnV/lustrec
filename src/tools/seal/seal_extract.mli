
val node_as_switched_sys:  Lustre_types.const_desc list -> (* mems  *) Lustre_types.var_decl list -> (* nd *) Lustre_types.node_desc -> (Lustre_types.expr option * Seal_utils.UpMap.key) list *
           (Lustre_types.expr option * Seal_utils.UpMap.key) list *
           (Lustre_types.expr option * Seal_utils.UpMap.key) list *
           (Lustre_types.expr option * Seal_utils.UpMap.key) list  

val fun_as_switched_sys: Lustre_types.const_desc list -> Lustre_types.node_desc -> (Lustre_types.expr option * (string * Lustre_types.expr) list) list
                                         
