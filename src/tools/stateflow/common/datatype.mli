open Basetypes

(* Type definitions of a model *)

type destination_t = DPath of path_t | DJunction of junction_name_t

type trans_t = {
  event : event_t;
  condition : Condition.t;
  condition_act : Action.t;
  transition_act : Action.t;
  dest : destination_t;
}

type transitions_t = trans_t list

type composition_t =
  | Or of transitions_t * state_name_t list
  | And of state_name_t list

type state_actions_t = {
  entry_act : Action.t;
  during_act : Action.t;
  exit_act : Action.t;
}

type state_def_t = {
  state_actions : state_actions_t;
  outer_trans : transitions_t;
  inner_trans : transitions_t;
  internal_composition : composition_t;
}

type 'prog_t src_components_t =
  | State of path_t * state_def_t
  | Junction of junction_name_t * transitions_t
  | SFFunction of 'prog_t

type prog_t =
  | Program of
      state_name_t
      * prog_t src_components_t list
      * (Lustre_types.var_decl * Lustre_types.expr) list

type trace_t = event_t list

module type MODEL_T = sig
  val name : string

  val model : prog_t

  val traces : trace_t list
end

(* Module (S)tate(F)low provides basic constructors for action, condition,
   events, as well as printer functions *)
module SF : sig
  val no_action : action_t

  val no_condition : condition_t

  val no_event : event_t

  val condition : base_condition_t -> condition_t

  val event : event_base_t -> event_t

  val state_action : action_t -> action_t -> action_t -> state_actions_t

  val states : prog_t -> ActiveStates.Vars.t

  val global_vars : prog_t -> (Lustre_types.var_decl * Lustre_types.expr) list

  val pp_dest : Format.formatter -> destination_t -> unit

  val pp_trans : Format.formatter -> trans_t -> unit

  val pp_transitions : Format.formatter -> trans_t list -> unit

  val pp_comp : Format.formatter -> composition_t -> unit
end
