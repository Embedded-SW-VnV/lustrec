open Utils

type label = ident

type type_dec = { ty_dec_desc : type_dec_desc; ty_dec_loc : Location.t }

and type_dec_desc =
  | Tydec_any
  | Tydec_int
  | Tydec_real
  (* | Tydec_float *)
  | Tydec_bool
  | Tydec_clock of type_dec_desc
  | Tydec_const of ident
  | Tydec_enum of ident list
  | Tydec_struct of (ident * type_dec_desc) list
  | Tydec_array of Dimension.t * type_dec_desc

type typedec_desc = { tydec_id : ident }

type typedef_desc = { tydef_id : ident; tydef_desc : type_dec_desc }

type clock_dec = { ck_dec_desc : clock_dec_desc; ck_dec_loc : Location.t }

and clock_dec_desc = Ckdec_any | Ckdec_bool of (ident * ident) list

type constant =
  | Const_int of int
  | Const_real of Real.t
  | Const_array of constant list
  | Const_tag of label
  | Const_string of string
  (* used only for annotations *)
  | Const_modeid of string
  (* used only for annotations *)
  | Const_struct of (label * constant) list

type quantifier_type = Exists | Forall

type var_decl = {
  var_id : ident;
  var_orig : bool;
  var_dec_type : type_dec;
  var_dec_clock : clock_dec;
  var_dec_const : bool;
  var_dec_value : expr option;
  mutable var_parent_nodeid : ident option;
  mutable var_type : Types.t;
  mutable var_clock : Clocks.t;
  var_loc : Location.t;
  var_is_contract: bool;
}
(* The tag of an expression is a unique identifier used to distinguish different
   instances of the same node *)

(** The core language and its ast. Every element of the ast contains its
    location in the program text. The type and clock of an ast element is
    mutable (and initialized to dummy values). This avoids to have to duplicate
    ast structures (e.g. ast, typed_ast, clocked_ast). *)

and expr = {
  expr_tag : tag;
  expr_desc : expr_desc;
  mutable expr_type : Types.t;
  mutable expr_clock : Clocks.t;
  mutable expr_delay : Delay.t;
  mutable expr_annot : expr_annot option;
  expr_loc : Location.t;
}

and expr_desc =
  | Expr_const of constant
  | Expr_ident of ident
  | Expr_tuple of expr list
  | Expr_ite of expr * expr * expr
  | Expr_arrow of expr * expr
  | Expr_fby of expr * expr
  | Expr_array of expr list
  | Expr_access of expr * Dimension.t
  | Expr_power of expr * Dimension.t
  | Expr_pre of expr
  | Expr_when of expr * ident * label
  | Expr_merge of ident * (label * expr) list
  | Expr_appl of call_t

and call_t = ident * expr * expr option
(* The third part denotes the boolean condition for resetting *)

and eq = { eq_lhs : ident list; eq_rhs : expr; eq_loc : Location.t }

(* The tag of an expression is a unique identifier used to distinguish different
   instances of the same node *)
and eexpr = {
  eexpr_tag : tag;
  eexpr_qfexpr : expr;
  eexpr_quantifiers : (quantifier_type * var_decl list) list;
  eexpr_name : string option;
  mutable eexpr_type : Types.t;
  mutable eexpr_clock : Clocks.t;
  (* mutable eexpr_normalized: (var_decl * eq list * var_decl list) option; *)
  eexpr_loc : Location.t;
}

and expr_annot = { annots : (string list * eexpr) list; annot_loc : Location.t }

type contract_mode = {
  mode_id : ident;
  require : eexpr list;
  ensure : eexpr list;
  mode_loc : Location.t;
}

type contract_import = {
  import_nodeid : ident;
  inputs : expr;
  outputs : expr;
  import_loc : Location.t;
}

type offset = Index of Dimension.t | Field of label

type assert_t = { assert_expr : expr; assert_loc : Location.t }

type statement = Eq of eq | Aut of automata_desc

and automata_desc = {
  aut_id : ident;
  aut_handlers : handler_desc list;
  aut_loc : Location.t;
}

and handler_desc = {
  hand_state : ident;
  hand_unless : (Location.t * expr * bool * ident) list;
  hand_until : (Location.t * expr * bool * ident) list;
  hand_locals : var_decl list;
  hand_stmts : statement list;
  hand_asserts : assert_t list;
  hand_annots : expr_annot list;
  hand_loc : Location.t;
}

type proof_annotation = Kinduction of int

type contract_desc = {
  consts : var_decl list;
  locals : var_decl list;
  stmts : statement list;
  assume : eexpr list;
  guarantees : eexpr list;
  modes : contract_mode list;
  imports : contract_import list;
  spec_loc : Location.t;
  proof : proof_annotation option
}

type 'a node_spec_t = Contract of 'a | NodeSpec of ident

type node_desc = {
  node_id : ident;
  mutable node_type : Types.t;
  mutable node_clock : Clocks.t;
  node_inputs : var_decl list;
  node_outputs : var_decl list;
  node_locals : var_decl list;
  mutable node_gencalls : expr list;
  mutable node_checks : Dimension.t list;
  node_asserts : assert_t list;
  node_stmts : statement list;
  mutable node_dec_stateless : bool;
  mutable node_stateless : bool option;
  node_spec : contract_desc node_spec_t option;
  node_annot : expr_annot list;
  node_iscontract : bool;
}

type imported_node_desc = {
  nodei_id : ident;
  mutable nodei_type : Types.t;
  mutable nodei_clock : Clocks.t;
  nodei_inputs : var_decl list;
  nodei_outputs : var_decl list;
  nodei_stateless : bool;
  nodei_spec : contract_desc node_spec_t option;
  (* nodei_annot: expr_annot list; *)
  nodei_prototype : string option;
  nodei_in_lib : string list;
  nodei_iscontract : bool;
}

type const_desc = {
  const_id : ident;
  const_loc : Location.t;
  const_value : constant;
  mutable const_type : Types.t;
}

type top_decl_desc =
  | Node of node_desc
  | Const of const_desc
  | ImportedNode of imported_node_desc
  | Open of bool * string
  (* the boolean set to true denotes a local lusi vs a lusi installed at system
     level *)
  | Include of string
  (* the boolean set to true denotes a local lus vs a lus installed at system
     level *)
  | TypeDef of typedef_desc

type top_decl = {
  top_decl_desc : top_decl_desc;
  (* description of the symbol *)
  top_decl_owner : Location.filename;
  (* the module where it is defined *)
  top_decl_itf : bool;
  (* header or source file ? *)
  top_decl_loc : Location.t;
}

type program_t = top_decl list

type dep_t = {
  local : bool;
  name : ident;
  content : program_t;
  is_stateful : bool;
}

type spec_types =
  | LocalContract of contract_desc
  | TopContract of top_decl list

val tag_true : label

val tag_false : label
