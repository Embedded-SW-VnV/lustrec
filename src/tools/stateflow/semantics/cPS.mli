module Semantics (T : CPS_transformer.TransformerType) (M : Datatype.MODEL_T) : sig
  val code_gen : bool * bool * bool -> Lustre_types.program_t
end
