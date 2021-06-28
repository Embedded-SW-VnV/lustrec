open Utils
open Format
open Lustre_types
open Machine_code_types
open C_backend_common

module type MODIFIERS_SRC = sig
  module GhostProto : MODIFIERS_GHOST_PROTO

  val pp_predicates : formatter -> machine_t list -> unit

  val pp_set_reset_spec : formatter -> ident -> ident -> machine_t -> unit

  val pp_clear_reset_spec : formatter -> ident -> ident -> machine_t -> unit

  val pp_step_spec :
    formatter -> machine_t list -> ident -> ident -> machine_t -> unit

  val pp_step_instr_spec :
    machine_t -> ident -> ident -> formatter -> instr_t -> unit

  val pp_ghost_parameter : ident -> formatter -> ident option -> unit
end

module EmptyMod : MODIFIERS_SRC

module Main (Mod : MODIFIERS_SRC) : sig
  val print_lib_c: formatter -> string -> program_t -> machine_t list -> dep_t list -> unit
end
