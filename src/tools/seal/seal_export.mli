val node_to_lustre: string (* basename *)
                    -> Lustre_types.top_decl list (* prog *)
                    -> Machine_code_types.machine_t (* machine *)
                    -> (Lustre_types.expr option * (string * Lustre_types.expr) list)
                         list (* sw_init *)
                    -> (Lustre_types.expr option * (string * Lustre_types.expr) list)
                         list (* sw_step *)
                    -> (Lustre_types.expr option * (string * Lustre_types.expr) list)
                         list (* init_out *)
                    -> (Lustre_types.expr option * (string * Lustre_types.expr) list)
                         list (* update_out*)
                    -> unit

val fun_to_lustre : string (* basename *)
                    -> Lustre_types.top_decl list (* prog *)
                    -> Machine_code_types.machine_t (* machine *)
                    -> ((Lustre_types.expr option * (string * Lustre_types.expr) list) list)
                    -> unit
