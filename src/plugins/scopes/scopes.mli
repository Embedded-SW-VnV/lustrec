open Utils
open Lustre_types

module Plugin : sig
  include PluginType.S

  val show_scopes : unit -> bool
end

(* (variable, node name, node instance) *)
type scope_t = (var_decl * string * string option) list * var_decl

val compute_scopes: ?first:bool -> program_t -> ident -> scope_t list

val pp_scopes: Format.formatter -> scope_t list -> unit
