(************ Machine code types *************)
open Lustre_types
open Spec_types

type value_t =
  {
    value_desc: value_t_desc;
    value_type: Types.type_expr;
    value_annot: expr_annot option
  }
and value_t_desc =
  | Cst of constant
  | Var of var_decl
  | Fun of ident * value_t list
  | Array of value_t list
  | Access of value_t * value_t
  | Power of value_t * value_t
  | ResetFlag

type mc_formula_t = value_t formula_t

type instr_t =
  {
    instr_desc: instr_t_desc; (* main data: the content *)
    (* lustre_expr: expr option; (* possible representation as a lustre expression *) *)
    lustre_eq: eq option;     (* possible representation as a lustre flow equation *)
    instr_spec: mc_formula_t list
  }
and instr_t_desc =
  | MLocalAssign of var_decl * value_t
  | MStateAssign of var_decl * value_t
  | MResetAssign of bool
  | MClearReset
  | MSetReset of ident
  | MNoReset of ident
  | MStep of var_decl list * ident * value_t list
  | MBranch of value_t * (label * instr_t list) list
  | MComment of string
  | MSpec of string 

type step_t = {
    step_checks: (Location.t * value_t) list;
    step_inputs: var_decl list;
    step_outputs: var_decl list;
    step_locals: var_decl list;
    step_instrs: instr_t list;
    step_asserts: value_t list;
  }

type static_call = top_decl * (Dimension.dim_expr list)

type mc_transition_t = value_t transition_t
type mc_memory_pack_t = value_t memory_pack_t

type machine_spec = {
  mnode_spec: node_spec_t option;
  mtransitions: mc_transition_t list;
  mmemory_packs: mc_memory_pack_t list
}
  
type machine_t = {
  mname: node_desc;
  mmemory: var_decl list;
  mcalls: (ident * static_call) list; (* map from stateful/stateless instance to node, no internals *)
  minstances: (ident * static_call) list; (* sub-map of mcalls, from stateful instance to node *)
  minit: instr_t list;
  mstatic: var_decl list; (* static inputs only *)
  mconst: instr_t list; (* assignments of node constant locals *)
  mstep: step_t;
  mspec: machine_spec;
  mannot: expr_annot list;
  msch: Scheduling_type.schedule_report option; (* Equations scheduling *)
}
