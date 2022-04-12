open Utils
open Lustre_types
open Machine_code_types

(* This functions produces an optimzed prog * machines It 1- eliminates common
   sub-expressions (TODO how is this different from normalization?) 2- inline
   constants and eliminate duplicated variables 3- try to reuse variables
   whenever possible

   When item (2) identified eliminated variables, the initial prog is modified,
   its normalized recomputed, as well as its scheduling, before regenerating the
   machines.

   The function returns both the (possibly updated) prog as well as the
   machines *)
val optimize :
  Normalization.param_t ->
  program_t ->
  Scheduling_type.schedule_report IMap.t ->
  machine_t list ->
  program_t * machine_t list
