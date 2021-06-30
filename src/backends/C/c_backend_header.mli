open Format
open Lustre_types
open Machine_code_types
open C_backend_common

module type MODIFIERS_HDR = sig
  module GhostProto : MODIFIERS_GHOST_PROTO

  val pp_machine_decl_prefix : formatter -> machine_t -> unit

  val pp_machine_ghost_struct : formatter -> machine_t -> unit

  val pp_import_arrow : formatter -> unit -> unit

  val pp_machine_alloc_decl : formatter -> machine_t -> unit
end

module EmptyMod : MODIFIERS_HDR

module Main (Mod : MODIFIERS_HDR) : sig
  val pp_header_from_header : formatter -> string -> top_decl list -> unit

  val pp_alloc_header :
    formatter -> string -> machine_t list -> dep_t list -> unit
end
