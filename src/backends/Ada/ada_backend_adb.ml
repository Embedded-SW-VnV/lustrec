(********************************************************************)
(*                                                                  *)
(*  The LustreC compiler toolset   /  The LustreC Development Team  *)
(*  Copyright 2012 -    --   ONERA - CNRS - INPT - ISAE-SUPAERO     *)
(*                                                                  *)
(*  LustreC is free software, distributed WITHOUT ANY WARRANTY      *)
(*  under the terms of the GNU Lesser General Public License        *)
(*  version 2.1.                                                    *)
(*                                                                  *)
(********************************************************************)

open Format

open Machine_code_types
open Lustre_types
open Corelang
open Machine_code_common
open Ada_backend_common

(** Main module for generating packages bodies
 **)
module Main =
struct

  (** Printing function for basic assignement [var_name := value].

      @param fmt the formater to print on
      @param var_name the name of the variable
      @param value the value to be assigned
   **)
  let pp_basic_assign m fmt var_name value =
    fprintf fmt "%a := %a"
      (pp_access_var m) var_name
      (pp_value m) value

  (** Printing function for instruction. See
      {!type:Machine_code_types.instr_t} for more details on
      machine types.

      @param typed_submachines list of all typed machine instances of this machine
      @param machine the current machine
      @param fmt the formater to print on
      @param instr the instruction to print
   **)
  let rec pp_machine_instr typed_submachines machine fmt instr =
    let pp_instr = pp_machine_instr typed_submachines machine in
    (* Print args for a step call *)
    let pp_state i fmt = fprintf fmt "%t.%s" pp_state_name i in
    let pp_args vl il fmt =
      fprintf fmt "@[%a@]%t@[%a@]"
        (Utils.fprintf_list ~sep:",@ " (pp_value machine)) vl
        (Utils.pp_final_char_if_non_empty ",@," il)
        (Utils.fprintf_list ~sep:",@ " pp_var_name) il
    in
    (* Print a when branch of a case *)
    let pp_when fmt (cond, instrs) =
      fprintf fmt "when %s =>@,%a" cond (pp_block pp_instr) instrs
    in
    (* Print a case *)
    let pp_case fmt (g, hl) =
      fprintf fmt "case %a is@,%aend case"
        (pp_value machine) g
        (pp_block pp_when) hl
    in
    (* Print a if *)
    (* If neg is true the we must test for the negation of the condition. It
       first check that we don't have a negation and a else case, if so it
       inverses the two branch and remove the negation doing a recursive
       call. *)
    let rec pp_if neg fmt (g, instrs1, instrs2) =
      match neg, instrs2 with
        | true, Some x -> pp_if false fmt (g, x, Some instrs1)
        | _ ->
          let pp_cond =
            if neg then
              fun fmt x -> fprintf fmt "! (%a)" (pp_value machine) x
            else
              pp_value machine
          in
          let pp_else = match instrs2 with
            | None -> fun fmt -> fprintf fmt ""
            | Some i2 -> fun fmt ->
                fprintf fmt "else@,%a" (pp_block pp_instr) i2
          in
          fprintf fmt "if %a then@,%a%tend if"
            pp_cond g
            (pp_block pp_instr) instrs1
            pp_else
    in
    match get_instr_desc instr with
      (* no reset *)
      | MNoReset _ -> ()
      (* reset  *)
      | MReset i when List.mem_assoc i typed_submachines ->
          let (substitution, submachine) = get_instance i typed_submachines in
          pp_package_call
            pp_reset_procedure_name
            fmt
            (substitution, submachine, pp_state i, None)
      | MLocalAssign (ident, value) ->
          pp_basic_assign machine fmt ident value
      | MStateAssign (ident, value) ->
          pp_basic_assign machine fmt ident value
      | MStep ([i0], i, vl) when is_builtin_fun i ->
          let value = mk_val (Fun (i, vl)) i0.var_type in
          pp_basic_assign machine fmt i0 value
      | MStep (il, i, vl) when List.mem_assoc i typed_submachines ->
          let (substitution, submachine) = get_instance i typed_submachines in
          pp_package_call
            pp_step_procedure_name
            fmt
            (substitution, submachine, pp_state i, Some (pp_args vl il))
      | MBranch (_, []) -> assert false
      | MBranch (g, (c1, i1)::tl) when c1=tag_false || c1=tag_true ->
          let neg = c1=tag_false in
          let other = match tl with
            | []         -> None
            | [(c2, i2)] -> Some i2
            | _          -> assert false
          in
          pp_if neg fmt (g, i1, other)
      | MBranch (g, hl) -> pp_case fmt (g, hl)
      | MComment s  ->
          let lines = String.split_on_char '\n' s in
          fprintf fmt "%a" (Utils.fprintf_list ~sep:"" pp_oneline_comment) lines
      | _ -> assert false

  (** Print the definition of the step procedure from a machine.

     @param typed_submachines list of all typed machine instances of this machine
     @param fmt the formater to print on
     @param machine the machine
  **)
  let pp_step_definition typed_submachines fmt m =
    pp_procedure_definition
      pp_step_procedure_name
      (pp_step_prototype m)
      (pp_machine_var_decl NoMode)
      (pp_machine_instr typed_submachines m)
      fmt
      (m.mstep.step_locals, m.mstep.step_instrs)

  (** Print the definition of the reset procedure from a machine.

     @param typed_submachines list of all typed machine instances of this machine
     @param fmt the formater to print on
     @param machine the machine
  **)
  let pp_reset_definition typed_submachines fmt m =
    let build_assign = function var ->
      mkinstr (MStateAssign (var, mk_default_value var.var_type))
    in
    let assigns = List.map build_assign m.mmemory in
    pp_procedure_definition
      pp_reset_procedure_name
      (pp_reset_prototype m)
      (pp_machine_var_decl NoMode)
      (pp_machine_instr typed_submachines m)
      fmt
      ([], assigns@m.minit)

  (** Print the package definition(ads) of a machine.
    It requires the list of all typed instance.
    A typed submachine instance is (ident, type_machine) with ident
    the instance name and typed_machine is (substitution, machine) with machine
    the machine associated to the instance and substitution the instanciation of
    all its polymorphic types.
     @param fmt the formater to print on
     @param typed_submachines list of all typed machine instances of this machine
     @param m the machine
  **)
  let pp_file fmt (typed_submachines, machine) =
    let pp_reset fmt =
      if is_machine_statefull machine then
        fprintf fmt "%a;@,@," (pp_reset_definition typed_submachines) machine
      else
        fprintf fmt ""
    in
    let aux pkgs (id, _) =
      try
        let (pkg, _) = List.assoc id ada_supported_funs in
        if List.mem pkg pkgs then
          pkgs
        else
          pkg::pkgs
      with Not_found -> pkgs
    in
    let packages = List.fold_left aux [] machine.mcalls in
    fprintf fmt "%a%t%a@,  @[<v>@,%t%a;@,@]@,%a;@."
      
      (* Include all the required packages*)
      (Utils.fprintf_list ~sep:";@," pp_with) packages
      (Utils.pp_final_char_if_non_empty ";@,@," packages)
      
      (*Begin the package*)
      (pp_begin_package true) machine
      
      (*Define the reset procedure*)
      pp_reset
      
      (*Define the step procedure*)
      (pp_step_definition typed_submachines) machine
      
      (*End the package*)
      pp_end_package machine

end

(* Local Variables: *)
(* compile-command: "make -C ../../.." *)
(* End: *)
