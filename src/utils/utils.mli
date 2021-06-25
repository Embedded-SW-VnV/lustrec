type ident = string
type tag = int

module IMap: sig
  include Map.S with type key = ident
  val pp: ?comment:string -> (Format.formatter -> 'a -> unit) -> Format.formatter -> 'a t -> unit
end

module ISet: sig
  include Set.S with type elt = ident
  val pp: Format.formatter -> t -> unit
end

module Format: sig
  include module type of Format
  val pp_print_semicolon: formatter -> unit -> unit
  val pp_open_vbox0: formatter -> unit -> unit
  val pp_print_cutcut: formatter -> unit -> unit
  val pp_print_nothing: formatter -> 'a -> unit
  val pp_print_list:
    ?pp_prologue:(formatter -> unit -> unit) ->
    ?pp_epilogue:(formatter -> unit -> unit) ->
    ?pp_op:(formatter -> unit -> unit) ->
    ?pp_cl:(formatter -> unit -> unit) ->
    ?pp_open_box:(formatter -> unit -> unit) ->
    ?pp_eol:(formatter -> unit -> unit) ->
    ?pp_nil:(formatter -> unit -> unit) ->
    ?pp_sep:(formatter -> unit -> unit) ->
    (formatter -> 'a -> unit) -> formatter -> 'a list -> unit
  val pp_comma_list:
    ?pp_prologue:(formatter -> unit -> unit) ->
    ?pp_epilogue:(formatter -> unit -> unit) ->
    ?pp_op:(formatter -> unit -> unit) ->
    ?pp_cl:(formatter -> unit -> unit) ->
    ?pp_open_box:(formatter -> unit -> unit) ->
    ?pp_eol:(formatter -> unit -> unit) ->
    ?pp_nil:(formatter -> unit -> unit) ->
    (formatter -> 'a -> unit) -> formatter -> 'a list -> unit
  val pp_print_parenthesized:
    ?pp_sep:(formatter -> unit -> unit) ->
    ?pp_prologue:(formatter -> unit -> unit) ->
    ?pp_epilogue:(formatter -> unit -> unit) ->
    ?pp_open_box:(formatter -> unit -> unit) ->
    ?pp_eol:(formatter -> unit -> unit) ->
    ?pp_nil:(formatter -> unit -> unit) ->
    (formatter -> 'a -> unit) -> formatter -> 'a list -> unit
  val pp_print_bracketed:
    ?pp_sep:(formatter -> unit -> unit) ->
    ?pp_prologue:(formatter -> unit -> unit) ->
    ?pp_epilogue:(formatter -> unit -> unit) ->
    ?pp_open_box:(formatter -> unit -> unit) ->
    ?pp_eol:(formatter -> unit -> unit) ->
    ?pp_nil:(formatter -> unit -> unit) ->
    (formatter -> 'a -> unit) -> formatter -> 'a list -> unit
end

module IdentDepGraph: Graph.Sig.I with type V.t = ident
module TopologicalDepGraph: sig
  val fold : (ident -> 'a -> 'a) -> IdentDepGraph.t -> 'a -> 'a
  val iter : (ident -> unit) -> IdentDepGraph.t -> unit
end

val name_of_dimension: tag -> ident

val name_of_carrier: tag -> ident

val name_of_type: tag -> ident

val name_of_delay: tag -> ident

val reset_names: unit -> unit

val pp_date: Format.formatter -> Unix.tm -> unit

exception TransposeError of int * int

val transpose_list: 'a list list -> 'a list list

val new_tag: unit -> tag

exception DeSome

val desome: 'a option -> 'a

val create_hashtable: int -> ('a * 'b) list -> ('a, 'b) Hashtbl.t

val option_map: ('a -> 'b) -> 'a option -> 'b option

val repeat: int -> ('a -> 'a) -> 'a -> 'a

val add_cons: 'a -> 'a list -> 'a list

val enumerate: int -> int list
