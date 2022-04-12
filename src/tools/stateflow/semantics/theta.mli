open Basetypes
open CPS_transformer

module KenvTheta (T : TransformerType) : sig
  type kenv_t = {
    cont_node :
      (path_t
      * ((kenv_t -> path_t -> frontier_t -> T.t)
        * (kenv_t -> T.t)
        * (kenv_t -> frontier_t -> T.t)))
      list;
    cont_junc :
      (junction_name_t
      * (kenv_t -> T.t wrapper_t -> T.t success_t -> T.t fail_t -> T.t))
      list;
  }

  module type KenvType = sig
    val kenv : kenv_t
  end

  module type MemoThetaTablesType = sig
    val tables : 'c call_t -> ('c, T.t) Memo.t
  end

  module type MemoThetaType = sig
    include ThetaType with type t = T.t

    val components : 'c call_t -> ('c * t) list
  end

  module type ModularType = sig
    val modular : (path_t, 'b, bool) tag_t -> path_t -> 'b
  end

  module type ThetaifyType = functor (Kenv : KenvType) -> MemoThetaType

  module MemoThetaTables () : MemoThetaTablesType

  module ModularThetaify (Tables : MemoThetaTablesType) (Mod : ModularType) :
    ThetaifyType
end
