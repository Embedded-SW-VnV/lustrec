open Utils
open Lustre_types

val mkhandler: Location.t -> ident ->  (Location.t * expr * bool * ident) list
  -> (Location.t * expr * bool * ident) list
  -> var_decl list
    -> statement list * assert_t list * expr_annot list -> handler_desc

val mkautomata: Location.t -> ident -> handler_desc list -> automata_desc

val expand_decls: program_t -> program_t

(* val expand_automata: (ident -> bool) -> (ident -> bool) -> ident -> typedef_desc -> node_desc ->
 *   automata_desc -> top_decl list * var_decl list * statement list *)
