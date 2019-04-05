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

open Misc_printer
open Misc_lustre_function
open Ada_printer
open Ada_backend_common

(** Main module for generating packages bodies
 **)
module Main =
struct

  (** Printing function for basic assignement [var := value].

      @param fmt the formater to print on
      @param var_name the name of the variable
      @param value the value to be assigned
   **)
  let pp_assign env fmt var value =
    fprintf fmt "%a := %a"
      (pp_var env) var
      (pp_value env) value

  (** Printing function for instruction. See
      {!type:Machine_code_types.instr_t} for more details on
      machine types.

      @param typed_submachines list of all typed machine instances of this machine
      @param machine the current machine
      @param fmt the formater to print on
      @param instr the instruction to print
   **)
  let rec pp_machine_instr typed_submachines env instr fmt =
    let pp_instr = pp_machine_instr typed_submachines env in
    (* Print args for a step call *)
    let pp_state i fmt = fprintf fmt "%t.%s" pp_state_name i in
    (* Print a when branch of a case *)
    let pp_when (cond, instrs) fmt =
      fprintf fmt "when %s =>@,%a" cond pp_block (List.map pp_instr instrs)
    in
    (* Print a case *)
    let pp_case fmt (g, hl) =
      fprintf fmt "case %a is@,%aend case"
        (pp_value env) g
        pp_block (List.map pp_when hl)
    in
    (* Print a if *)
    (* If neg is true the we must test for the negation of the condition. It
       first check that we don't have a negation and a else case, if so it
       inverses the two branch and remove the negation doing a recursive
       call. *)
    let pp_if fmt (neg, g, instrs1, instrs2) =
      let pp_cond =
        if neg then
          fun fmt x -> fprintf fmt "! (%a)" (pp_value env) x
        else
          pp_value env
      in
      let pp_else = match instrs2 with
        | None -> fun fmt -> fprintf fmt ""
        | Some i2 -> fun fmt ->
            fprintf fmt "else@,%a" pp_block (List.map pp_instr i2)
      in
      fprintf fmt "if %a then@,%a%tend if"
        pp_cond g
        pp_block (List.map pp_instr instrs1)
        pp_else
    in
    match get_instr_desc instr with
      (* no reset *)
      | MNoReset _ -> ()
      (* reset  *)
      | MReset i when List.mem_assoc i typed_submachines ->
          let (substitution, submachine) = get_instance i typed_submachines in
          let pp_package = pp_package_name_with_polymorphic substitution submachine in
          let args = if is_machine_statefull submachine then [[pp_state i]] else [] in
          pp_call fmt (pp_package_access (pp_package, pp_reset_procedure_name), args)
      | MLocalAssign (ident, value) ->
          pp_assign env fmt ident value
      | MStateAssign (ident, value) ->
          pp_assign env fmt ident value
      | MStep ([i0], i, vl) when is_builtin_fun i ->
          let value = mk_val (Fun (i, vl)) i0.var_type in
            pp_assign env fmt i0 value
      | MStep (il, i, vl) when List.mem_assoc i typed_submachines ->
          let (substitution, submachine) = get_instance i typed_submachines in
          let pp_package = pp_package_name_with_polymorphic substitution submachine in
          let input = List.map (fun x fmt -> pp_value env fmt x) vl in
          let output = List.map pp_var_name il in
          let args =
            (if is_machine_statefull submachine then [[pp_state i]] else [])
              @(if input!=[] then [input] else [])
              @(if output!=[] then [output] else [])
          in
          pp_call fmt (pp_package_access (pp_package, pp_step_procedure_name), args)
      | MBranch (_, []) -> assert false
      | MBranch (g, (c1, i1)::tl) when c1=tag_false || c1=tag_true ->
          pp_if fmt (build_if g c1 i1 tl)
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
  let pp_step_definition env typed_submachines fmt (m, m_spec_opt) =
    let transform_local_to_state_assign instr = match instr.instr_desc with
      | MLocalAssign (ident, value) -> 
          { instr_desc = MStateAssign (ident, value);
            lustre_eq= instr.lustre_eq }
      | x -> instr
    in
    let spec_instrs = match m_spec_opt with
      | None -> []
      | Some m_spec -> List.map transform_local_to_state_assign m_spec.mstep.step_instrs
    in
    let pp_local_list = List.map (build_pp_var_decl_local None) (m.mstep.step_locals) in
    let pp_instr_list = List.map (pp_machine_instr typed_submachines env) (m.mstep.step_instrs@spec_instrs) in
    let content = AdaProcedureContent ((if pp_local_list = [] then [] else [pp_local_list]), pp_instr_list) in
    pp_procedure pp_step_procedure_name (build_pp_arg_step m) None fmt content

  (** Print the definition of the reset procedure from a machine.

     @param typed_submachines list of all typed machine instances of this machine
     @param fmt the formater to print on
     @param machine the machine
  **)
  let pp_reset_definition env typed_submachines fmt m =
    let build_assign = function var ->
      mkinstr (MStateAssign (var, mk_default_value var.var_type))
    in
    let assigns = List.map build_assign m.mmemory in
    let pp_instr_list = List.map (pp_machine_instr typed_submachines env) (assigns@m.minit) in
    pp_procedure pp_reset_procedure_name (build_pp_arg_reset m) None fmt (AdaProcedureContent ([], pp_instr_list))

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
  let pp_file fmt (typed_submachines, ((opt_spec_machine, guarantees), machine)) =
    let env = List.map (fun x -> x.var_id, pp_state_name) machine.mmemory in
    let pp_reset fmt =
      if is_machine_statefull machine then
        fprintf fmt "%a;@,@," (pp_reset_definition env typed_submachines) machine
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
    let packages = List.map pp_str (List.fold_left aux [] machine.mcalls) in
    let pp_content fmt =
      fprintf fmt "%t%a"
        (*Define the reset procedure*)
        pp_reset
        
        (*Define the step procedure*)
        (pp_step_definition env typed_submachines) (machine, opt_spec_machine)
    in
    fprintf fmt "%a%t%a;@."
      
      (* Include all the required packages*)
      (Utils.fprintf_list ~sep:";@," (pp_with AdaNoVisibility)) packages
      (Utils.pp_final_char_if_non_empty ";@,@," packages)
      
      (*Print package*)
      (pp_package (pp_package_name machine) [] true ) pp_content

end

(* Local Variables: *)
(* compile-command: "make -C ../../.." *)
(* End: *)
