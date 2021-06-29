open Basetypes
open Datatype
open CPS_transformer
open Theta

module Interpreter (Transformer : TransformerType): sig

  (* module KT = KenvTheta (Transformer) *)

  module type ProgType = sig
    val init : state_name_t

    val defs : prog_t src_components_t list
  end

  module type EvaluationType = sig
    module Theta : ThetaType with type t = Transformer.t

    val eval_prog : Transformer.t

    val eval_components : 'c call_t -> ('c * Transformer.t) list
  end

  module Evaluation
      (Thetaify : KenvTheta(Transformer).ThetaifyType)
      (Prog : ProgType) :
    EvaluationType
end
