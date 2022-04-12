open Utils

val expr_annotations : (string list, ident * tag) Hashtbl.t

val add_node_ann : ident -> string list -> unit

val add_expr_ann : ident -> tag -> string list -> unit

val get_expr_annotations : ident list -> (ident * tag) list
