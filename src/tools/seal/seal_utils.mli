val report: ?verbose_level:int ->
           level:int -> (Format.formatter -> unit) -> unit

val seal_debug: bool ref 

type 'boolexpr guard = 'boolexpr list

type ('guard, 'elem) guarded_expr = 'guard * 'elem

type element = IsInit | Expr of Lustre_types.expr

type elem_boolexpr = element * bool

type elem_guarded_expr = (elem_boolexpr guard, element) guarded_expr

type 'ge mdef_t = 'ge list

val pp_up: (Format.formatter -> 'a -> unit) -> Format.formatter -> (string * 'a) mdef_t -> unit
  
val pp_sys :
  (Format.formatter -> 'update_expr -> unit) ->
  Format.formatter ->
  (Lustre_types.expr option * (Utils.ident * 'update_expr) list) list -> unit

val pp_guard_list: (Format.formatter -> 'a -> unit) -> Format.formatter -> ('a * bool) mdef_t -> unit

val pp_elem: Format.formatter -> element -> unit

val pp_assign_map : (Format.formatter -> 'a -> unit) -> Format.formatter -> (string * (('a * bool) mdef_t * 'a) mdef_t) mdef_t -> unit
  
val deelem : element -> Lustre_types.expr
                          
val pp_guard_expr: (Format.formatter -> element -> unit) -> Format.formatter -> elem_boolexpr list * element -> unit

val select_elem:  element -> elem_boolexpr -> bool 

val pp_mdefs:  (Format.formatter -> element -> unit) -> Format.formatter -> (elem_boolexpr list * element) mdef_t -> unit

val pp_all_defs: Format.formatter -> (Utils.ident * (elem_boolexpr list * element) mdef_t) list -> unit


module Guards : sig
  include Set.S
  val pp_short: Format.formatter -> t -> unit
  val pp_long: Format.formatter -> t -> unit
    
end with type elt = Lustre_types.expr * bool


module UpMap : sig
  include Map.S
  val pp: Format.formatter -> (string * Lustre_types.expr) mdef_t -> unit
end with type key = (string * Lustre_types.expr) mdef_t
