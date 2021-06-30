open Format
open Lustre_types
open Machine_code_types

module type MODIFIERS_MAINSRC = sig end

module EmptyMod : MODIFIERS_MAINSRC

module Main (Mod : MODIFIERS_MAINSRC) : sig
  val print_main_c :
    formatter ->
    machine_t ->
    string ->
    program_t ->
    machine_t list ->
    dep_t list ->
    unit
end
