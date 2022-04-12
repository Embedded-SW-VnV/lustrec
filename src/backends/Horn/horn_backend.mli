val translate :
  Format.formatter ->
  Lustre_types.program_t ->
  Machine_code_types.machine_t list ->
  unit

val preprocess: Machine_code_types.machine_t list ->
                Machine_code_types.machine_t list 
  
