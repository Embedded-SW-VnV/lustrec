open Utils
open Lustre_types

val analyze: program_t -> program_t * Scheduling_type.schedule_report IMap.t
