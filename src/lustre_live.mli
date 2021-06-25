open Utils
open Lustre_types

val inter_live_i_with: ident -> int -> var_decl list -> var_decl list
val set_live_of: ident -> var_decl list -> var_decl list -> eq list -> unit
val existential_vars: ident -> int -> eq -> var_decl list -> var_decl list
