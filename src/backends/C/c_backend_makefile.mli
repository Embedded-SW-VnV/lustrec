open Utils
open Format
open Lustre_types

module type MODIFIERS_MKF = sig
  val other_targets : formatter -> string -> string -> dep_t list -> unit
end

module EmptyMod : MODIFIERS_MKF

module Main (Mod : MODIFIERS_MKF) : sig
  val print_makefile : string -> string -> dep_t list -> formatter -> unit
end

val fprintf_dependencies : formatter -> dep_t list -> unit

val compiled_dependencies : dep_t list -> dep_t list

val lib_dependencies : dep_t list -> ident list
