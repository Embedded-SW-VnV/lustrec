type t = { mutable ddesc : delay_desc; did : int }

and delay_desc =
  | Dvar (* Monomorphic type variable *)
  | Dundef
  | Darrow of t * t
  | Dtuple of t list
  | Dlink of t
  (* During unification, make links instead of substitutions *)
  | Dunivar
(* Polymorphic type variable *)

val new_var : unit -> t

val new_univar : unit -> t

val new_delay : delay_desc -> t
