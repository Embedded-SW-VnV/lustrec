type state_name_t = string

type junction_name_t = string

type path_t = state_name_t list

type event_base_t = string

type event_t = event_base_t option

type user_variable_name_t = string

(* Connected to lustrec types *)
type base_action_t = {
  defs : Lustre_types.statement list;
  ainputs : Lustre_types.var_decl list;
  aoutputs : Lustre_types.var_decl list;
  avariables : Lustre_types.var_decl list; (* ident: string; *)
}

type base_condition_t = {
  expr : Lustre_types.expr;
  cinputs : Lustre_types.var_decl list;
  coutputs : Lustre_types.var_decl list;
  cvariables : Lustre_types.var_decl list;
}

val pp_state_name: Format.formatter -> state_name_t -> unit
val pp_junction_name: Format.formatter -> junction_name_t -> unit
val pp_path: Format.formatter -> path_t -> unit

type frontier_t = Loose | Strict

type _ call_t =
  | Ecall : (path_t * path_t * frontier_t) call_t
  | Dcall : path_t call_t
  | Xcall : (path_t * frontier_t) call_t

(* Conditions are either (1) simple strings, (2) the active status of a state or
   (3) occurence of an event. They can be combined (conjunction, negation) *)
module type ConditionType = sig
  type t

  val cquote : base_condition_t -> t

  val tru : t

  val active : path_t -> t

  val event : event_t -> t

  val ( && ) : t -> t -> t

  val neg : t -> t

  val pp_cond : Format.formatter -> t -> unit
end

module Condition: ConditionType

module type ActionType = sig
  type t

  val nil : t

  val aquote : base_action_t -> t

  val open_path : path_t -> t

  val close_path : path_t -> t

  val call : 'c call_t -> 'c -> t

  val pp_act : Format.formatter -> t -> unit
end

module Action: ActionType
