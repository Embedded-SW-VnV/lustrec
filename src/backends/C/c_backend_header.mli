open Format
open Lustre_types
open Machine_code_types
open C_backend_common

module type MODIFIERS_HDR = sig
  module GhostProto : MODIFIERS_GHOST_PROTO

  val print_machine_decl_prefix : formatter -> machine_t -> unit

  val pp_import_arrow : formatter -> unit -> unit
end

module EmptyMod : MODIFIERS_HDR

module Main (Mod : MODIFIERS_HDR) : sig
  val print_header_from_header : formatter -> string -> top_decl list -> unit

  val print_alloc_header :
    formatter -> string -> machine_t list -> dep_t list -> unit
end
