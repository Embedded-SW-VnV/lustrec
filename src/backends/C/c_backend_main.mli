open Utils
open Format
open Lustre_types
open Machine_code_types

module type MODIFIERS_MAINSRC = sig
  val pp_declare_ghost_state : formatter -> ident -> unit

  val pp_ghost_state_parameter : formatter -> unit -> unit

  val pp_main_spec : formatter -> machine_t -> unit
end

module EmptyMod : MODIFIERS_MAINSRC

module Main (Mod : MODIFIERS_MAINSRC) : sig
  val pp_main_c :
    formatter ->
    machine_t ->
    string ->
    program_t ->
    machine_t list ->
    dep_t list ->
    unit
end
