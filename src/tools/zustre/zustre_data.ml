let ctx = ref (Z3.mk_context [])

let fp = ref (Z3.Fixedpoint.mk_fixedpoint !ctx)

let const_sorts : (Utils.ident, Z3.Sort.sort) Hashtbl.t =
  Hashtbl.create 13

let const_tags : (Utils.ident, Z3.Sort.sort) Hashtbl.t =
  Hashtbl.create 13

let sort_elems : (Z3.Sort.sort, Utils.ident list) Hashtbl.t =
  Hashtbl.create 13

let decls : (Utils.ident, Z3.FuncDecl.func_decl) Hashtbl.t =
  Hashtbl.create 13

let debug = ref false

let timeout = ref 10000
(* default : 10 s = 10 000 ms *)

(* Local Variables: *)
(* compile-command:"make -C ../.." *)
(* End: *)
