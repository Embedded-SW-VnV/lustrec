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

(** Functions printing the .ads file **)
module Main =
struct

  (** Print a new statement instantiating a generic package.
     @param fmt the formater to print on
     @param substitutions the instanciation substitution
     @param machine the machine to instanciate
  **)
  let pp_new_package fmt (substitutions, machine) =
    let pp_name = pp_package_name machine in
    let pp_new_name = pp_package_name_with_polymorphic substitutions machine in
    let instanciations = List.map (fun (id, typ) -> (pp_polymorphic_type id, fun fmt -> pp_type fmt typ)) substitutions in
    pp_package_instanciation pp_new_name pp_name fmt instanciations

  (** Print a precondition in aspect
     @param fmt the formater to print on
     @param expr the expession to print as pre
  **)
  let pp_pre fmt expr =
    fprintf fmt "Pre => %a"
      pp_clean_ada_identifier expr

  (** Print a postcondition in aspect
     @param fmt the formater to print on
     @param expr the expession to print as pre
  **)
  let pp_post fmt ident =
    fprintf fmt "Post => %a"
      pp_clean_ada_identifier ident

  (** Print the declaration of a procedure with a contract
     @param pp_prototype the prototype printer
     @param fmt the formater to print on
     @param contract the contract for the function to declare
  **)
  let pp_contract guarantees fmt =
    fprintf fmt "@,  @[<v>Global => null%t%a@]"
      (Utils.pp_final_char_if_non_empty ",@," guarantees)
      (Utils.fprintf_list ~sep:",@," pp_post) guarantees

(*
  let pp_transition_name fmt = fprintf fmt "transition"
  let pp_state_name_transition suffix fmt = fprintf fmt "%t_%s" pp_state_name suffix

  (** Printing function for basic assignement [var_name := value].

      @param fmt the formater to print on
      @param var_name the name of the variable
      @param value the value to be assigned
   **)
  let pp_basic_assign m fmt var_name value =
    fprintf fmt "%a = %a"
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
  let rec pp_machine_instr typed_submachines machine instr fmt =
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
    let pp_when (cond, instrs) fmt =
      fprintf fmt "when %s =>@,%a" cond pp_block (List.map pp_instr instrs)
    in
    (* Print a case *)
    let pp_case fmt (g, hl) =
      fprintf fmt "case %a is@,%aend case"
        (pp_value machine) g
        pp_block (List.map pp_when hl)
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
          pp_call fmt (pp_package_access (pp_package, pp_name), [pp_state i])
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

  (** Print the expression function representing the transition predicate.
     @param fmt the formater to print on
     @param machine the machine
  **)
  let pp_transition_predicate typed_submachines fmt (opt_spec_machine, m) =
    let spec_instrs = match opt_spec_machine with
      | None -> []
      | Some m -> m.mstep.step_instrs
    in
    fprintf fmt "function %t (%a; %a) return Boolean is (@,  @[<v>%a@,@]) with Ghost"
      pp_transition_name
      pp_var_decl_mode (In, pp_state_name_transition "old", pp_state_type)
      pp_var_decl_mode (In, pp_state_name_transition "new", pp_state_type)
      (Utils.fprintf_list ~sep:" and@," (pp_machine_instr typed_submachines m)) (m.mstep.step_instrs@spec_instrs)*)
    
  (** Remove duplicates from a list according to a given predicate.
     @param eq the predicate defining equality
     @param l the list to parse
  **)
  let remove_duplicates eq l =
    let aux l x = if List.exists (eq x) l then l else x::l in
    List.fold_left aux [] l


  (** Compare two typed machines.
  **)
  let eq_typed_machine (subst1, machine1) (subst2, machine2) =
    (String.equal machine1.mname.node_id machine2.mname.node_id) &&
    (List.for_all2 (fun a b -> pp_eq_type (snd a) (snd b)) subst1 subst2)


  (** Print the package declaration(ads) of a machine.
    It requires the list of all typed instance.
    A typed submachine is a (ident, typed_machine) with
      - ident: the name 
      - typed_machine: a (substitution, machine) with
        - machine: the submachine struct
        - substitution the instanciation of all its polymorphic types.
     @param fmt the formater to print on
     @param typed_submachines list of all typed submachines of this machine
     @param m the machine
  **)
  let pp_file fmt (typed_submachines, ((opt_spec_machine, guarantees), m)) =
    let typed_machines = snd (List.split typed_submachines) in
    let typed_machines_set = remove_duplicates eq_typed_machine typed_machines in
    
    let machines_to_import = List.map pp_package_name (snd (List.split typed_machines_set)) in

    let polymorphic_types = find_all_polymorphic_type m in
    
    let typed_machines_to_instanciate =
      List.filter (fun (l, _) -> l != []) typed_machines_set in

    let typed_instances = List.filter is_submachine_statefull typed_submachines in

    let pp_state_decl_and_reset fmt = fprintf fmt "%t;@,@,%a;@,@,"
      (*Declare the state type*)
      (pp_type_decl pp_state_type AdaLimitedPrivate)
      (*Declare the reset procedure*)
      (pp_procedure pp_reset_procedure_name (build_pp_arg_reset m) None) AdaNoContent
    in

    let vars = List.map (build_pp_var_decl AdaNoMode) m.mmemory in
    let states = List.map build_pp_state_decl_from_subinstance typed_instances in
    let var_lists = (if vars = [] then [] else [vars])@(if states = [] then [] else [states]) in

    let pp_private_section fmt = fprintf fmt "@,private@,@,%a%t%a"
      (*Instantiate the polymorphic type that need to be instantiated*)
      (Utils.fprintf_list ~sep:";@," pp_new_package) typed_machines_to_instanciate
      (Utils.pp_final_char_if_non_empty ";@,@," typed_machines_to_instanciate)
      (*Define the state type*)
      (pp_record pp_state_type) var_lists
    in
    
    let pp_ifstatefull fmt pp =
      if is_machine_statefull m then
        fprintf fmt "%t" pp
      else
        fprintf fmt ""
    in

    let pp_content fmt =
      let pp_contract_opt = match guarantees with
                              | [] -> None
                              | _ ->  Some (pp_contract guarantees) in
      fprintf fmt "%a%a%a%a" (* %a;@, *)
        pp_ifstatefull pp_state_decl_and_reset
        
        (*Declare the transition predicate*)
        (* pp_transition_predicate typed_submachines) (opt_spec_machine, m) *)
        
        (*Declare the step procedure*)
        (pp_procedure pp_step_procedure_name (build_pp_arg_step m) pp_contract_opt) AdaNoContent
        
        pp_ifstatefull (fun fmt -> fprintf fmt ";@,")
        
        (*Print the private section*)
        pp_ifstatefull pp_private_section
    in
    
    let pp_poly_types id = pp_type_decl (pp_polymorphic_type id) AdaPrivate in
    let pp_generics = List.map pp_poly_types polymorphic_types in
    
    fprintf fmt "@[<v>%a%t%a;@]@."
      
      (* Include all the subinstance package*)
      (Utils.fprintf_list ~sep:";@," (pp_with AdaPrivate)) machines_to_import
      (Utils.pp_final_char_if_non_empty ";@,@," machines_to_import)
      
      (*Begin the package*)
      (pp_package (pp_package_name m) pp_generics false) pp_content

end
