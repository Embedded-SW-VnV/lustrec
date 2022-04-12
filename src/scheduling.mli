open Utils
open Format
open Lustre_types
open Scheduling_type

val schedule_node : node_desc -> schedule_report

val schedule_prog : program_t -> program_t * schedule_report IMap.t

val remove_prog_inlined_locals :
  'a IMap.t IMap.t -> schedule_report IMap.t -> schedule_report IMap.t

val compute_prog_reuse_table :
  schedule_report IMap.t -> (ident, var_decl) Hashtbl.t IMap.t

val sort_equations_from_schedule :
  eq list -> ident list list -> eq list * ident list

val pp_warning_unused : formatter -> schedule_report IMap.t -> unit

val pp_schedule : formatter -> schedule_report IMap.t -> unit

val pp_fanin_table : formatter -> schedule_report IMap.t -> unit

val pp_dep_graph : formatter -> schedule_report IMap.t -> unit
