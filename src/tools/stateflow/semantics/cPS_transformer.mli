open Basetypes

type mode_t = Outer | Inner | Enter

type 't success_t = path_t -> 't

type 't fail_t = { local : 't; global : 't }

type 't wrapper_t = path_t -> 't -> 't

type ('a, 'b, 't) tag_t =
  | E : (path_t, path_t -> frontier_t -> 't, 't) tag_t
  | D : (path_t, 't, 't) tag_t
  | X : (path_t, frontier_t -> 't, 't) tag_t
  | J
      : ( junction_name_t,
          't wrapper_t -> 't success_t -> 't fail_t -> 't,
          't )
        tag_t

type ('a, 'b, 't) theta_t = ('a, 'b, 't) tag_t -> 'a -> 'b

module type ThetaType = sig
  type t

  val theta : ('a, 'b, t) theta_t
end

val pp_mode: Format.formatter -> mode_t -> unit
val pp_tag: Format.formatter -> ('a, 'b, 't) tag_t -> unit

module type TransformerType = sig
  type act_t = Action.t

  type cond_t = Condition.t

  type t

  include ActionType with type t := act_t

  include ConditionType with type t := cond_t

  val null : t

  val bot : t

  val ( >> ) : t -> t -> t

  val eval_act : (module ThetaType with type t = t) -> act_t -> t

  val eval_cond : cond_t -> t -> t -> t

  (* val mktransformer : t -> unit *)
  val mkprincipal : t -> Lustre_types.program_t

  val mkcomponent : 'c call_t -> 'c -> t -> Lustre_types.program_t
end

module type ComparableTransformerType = sig
  include TransformerType

  val ( == ) : t -> t -> bool
end

module TransformerStub: sig
  type act_t = Action.t
  type cond_t = Condition.t
  include ConditionType with type t := cond_t
  include ActionType with type t := act_t
end
