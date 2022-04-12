open Basetypes
open CPS_transformer

module LustrePrinter (Vars : sig
  val state_vars : ActiveStates.Vars.t

  val global_vars : GlobalVarDef.t list
end) : TransformerType
