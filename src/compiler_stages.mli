open Lustre_types
open Machine_code_types

exception StopPhase1 of program_t

val stage1 :
  Normalization.param_t ->
  program_t ->
  string ->
  string ->
  string ->
  program_t * dep_t list

val stage2 : Normalization.param_t -> program_t -> program_t * machine_t list

val stage3 :
  program_t -> machine_t list -> dep_t list -> string -> string -> unit
