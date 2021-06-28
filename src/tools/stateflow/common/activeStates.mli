module Vars: Set.S with type elt = Basetypes.path_t

module Env: sig
  include Map.S with type key = Basetypes.path_t

  val from_set: Vars.t -> 'a -> 'a t
end
