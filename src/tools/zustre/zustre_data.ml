let ctx = ref (Z3.mk_context [])
let fp = ref (Z3.Fixedpoint.mk_fixedpoint !ctx)


let const_sorts : (Lustre_types.ident, Z3.Sort.sort) Hashtbl.t = Hashtbl.create 13
let const_tags : (Lustre_types.ident, Z3.Sort.sort) Hashtbl.t = Hashtbl.create 13
let sort_elems : (Z3.Sort.sort, Lustre_types.ident list) Hashtbl.t = Hashtbl.create 13


let decls: (Lustre_types.ident, Z3.FuncDecl.func_decl) Hashtbl.t = Hashtbl.create 13


(* Local Variables: *)
(* compile-command:"make -C ../.." *)
(* End: *)
