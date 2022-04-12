val ctx: Z3.context ref
val fp:  Z3.Fixedpoint.fixedpoint ref
val const_sorts: (Utils.ident, Z3.Sort.sort) Hashtbl.t
val const_tags: (Utils.ident, Z3.Sort.sort) Hashtbl.t
val sort_elems: (Z3.Sort.sort, Utils.ident list) Hashtbl.t
val decls : (Utils.ident, Z3.FuncDecl.func_decl) Hashtbl.t
val debug: bool ref
val timeout: int ref
