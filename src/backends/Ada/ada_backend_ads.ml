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


  let suffixOld = "_old"
  let suffixNew = "_new"
  let pp_transition_name fmt = fprintf fmt "transition"
  let pp_state_name_transition suffix fmt = fprintf fmt "%t%s" pp_state_name suffix




  (** Printing function for basic assignement [var := value].

      @param fmt the formater to print on
      @param var_name the name of the variable
      @param value the value to be assigned
   **)
  let pp_local_eq env fmt var value =
    fprintf fmt "%t = %a"
      (pp_var_name var)
      (pp_value env) value

  (** Printing function for basic assignement [var := value].

      @param fmt the formater to print on
      @param var_name the name of the variable
      @param value the value to be assigned
   **)
  let pp_state_eq env fmt var value =
    fprintf fmt "%t = %a"
      (pp_access (pp_state_name_transition suffixNew) (pp_var_name var))
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
    let pp_state suffix i fmt = fprintf fmt "%t.%s" (pp_state_name_transition suffix) i in
    match get_instr_desc instr with
      (* no reset *)
      | MNoReset _ -> ()
      (* reset  *)
      | MReset i when List.mem_assoc i typed_submachines ->
          let (substitution, submachine) = get_instance i typed_submachines in
          let pp_package = pp_package_name_with_polymorphic substitution submachine in
          let args = if is_machine_statefull submachine then [[pp_state suffixOld i;pp_state suffixNew i]] else [] in
          pp_call fmt (pp_package_access (pp_package, pp_reset_procedure_name), args)
      | MLocalAssign (ident, value) ->
          pp_local_eq env fmt ident value
      | MStateAssign (ident, value) ->
          pp_state_eq env fmt ident value
      | MStep ([i0], i, vl) when is_builtin_fun i ->
          let value = mk_val (Fun (i, vl)) i0.var_type in
          if List.mem_assoc i0.var_id env then
            pp_state_eq env fmt i0 value
          else
            pp_local_eq env fmt i0 value
          
      | MStep (il, i, vl) when List.mem_assoc i typed_submachines ->
          let (substitution, submachine) = get_instance i typed_submachines in
          let pp_package = pp_package_name_with_polymorphic substitution submachine in
          let input = List.map (fun x fmt -> pp_value env fmt x) vl in
          let output = List.map pp_var_name il in
          let args =
            (if is_machine_statefull submachine then [[pp_state suffixOld i;pp_state suffixNew i]] else [])
              @(if input!=[] then [input] else [])
              @(if output!=[] then [output] else [])
          in
          fprintf fmt "(%a)" pp_call (pp_package_access (pp_package, pp_transition_name), args)
      | MComment s -> ()
      | _ -> assert false


















  (** Print the expression function representing the transition predicate.
     @param fmt the formater to print on
     @param machine the machine
  **)
  let pp_transition_predicate prototype typed_submachines fmt (opt_spec_machine, m) =
    let old_state = (AdaIn, pp_state_name_transition suffixOld, pp_state_type, None) in
    let new_state = (AdaIn, pp_state_name_transition suffixNew, pp_state_type, None) in
    let env = List.map (fun x -> x.var_id, pp_state_name_transition suffixOld) m.mmemory in
    let inputs = build_pp_var_decl_step_input AdaIn None m in
    let outputs = build_pp_var_decl_step_output AdaIn None m in
    let instrs = push_if_in_expr m.mstep.step_instrs in
    let content = List.map (pp_machine_instr typed_submachines env) instrs in
    let locals = List.map (fun x-> (pp_var_name x, fun fmt -> pp_var_type fmt x)) m.mstep.step_locals in
    pp_predicate pp_transition_name ([[old_state; new_state]]@inputs@outputs) fmt (if prototype then None else Some (locals, content))
    












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
  let pp_file fmt (typed_submachines, ((m_spec_opt, guarantees), m)) =
    let typed_machines = snd (List.split typed_submachines) in
    let typed_machines_set = remove_duplicates eq_typed_machine typed_machines in
    
    let machines_to_import = List.map pp_package_name (snd (List.split typed_machines_set)) in

    let polymorphic_types = find_all_polymorphic_type m in
    
    let typed_machines_to_instanciate =
      List.filter (fun (l, _) -> l != []) typed_machines_set in

    let typed_instances = List.filter is_submachine_statefull typed_submachines in

    let pp_state_decl_and_reset fmt = fprintf fmt "%t;@,@,%a;@,@,"
      (*Declare the state type*)
      (pp_type_decl pp_state_type AdaPrivate)
      (*Declare the reset procedure*)
      (pp_procedure pp_reset_procedure_name (build_pp_arg_reset m) None) AdaNoContent
    in
    
    let vars_spec = match m_spec_opt with
      | None -> []
      | Some m_spec -> List.map (build_pp_var_decl AdaNoMode None) m_spec.mstep.step_locals
    in
    let vars = List.map (build_pp_var_decl AdaNoMode None) m.mmemory in
    let states = List.map (build_pp_state_decl_from_subinstance AdaNoMode None) typed_instances in
    let var_lists =
      (if states = [] then [] else [states]) @
      (if vars = [] then [] else [vars])@
      (if vars_spec = [] then [] else [vars_spec]) in
    
    let pp_ifstatefull fmt pp =
      if is_machine_statefull m then
        fprintf fmt "%t" pp
      else
        fprintf fmt ""
    in

    let pp_private_section fmt = fprintf fmt "@,private@,@,%a%t%a;@,@,%a"
      (*Instantiate the polymorphic type that need to be instantiated*)
      (Utils.fprintf_list ~sep:";@," pp_new_package) typed_machines_to_instanciate
      (Utils.pp_final_char_if_non_empty ";@,@," typed_machines_to_instanciate)
      (*Define the state type*)
      pp_ifstatefull (fun fmt-> pp_record pp_state_type fmt var_lists)
        
      (*Declare the transition predicate*)
      (pp_transition_predicate false typed_submachines) (m_spec_opt, m)
    in

    let pp_content fmt =
      let pp_contract_opt =
        let ghost_memory = match m_spec_opt with
          | None -> []
          | Some m_spec -> m_spec.mstep.step_locals
        in
        let pp_var x fmt =
          if List.exists (fun var -> var.var_id == x) ghost_memory then
            pp_access pp_state_name (fun fmt -> pp_clean_ada_identifier fmt x) fmt
          else
            pp_clean_ada_identifier fmt x
        in
        let input = List.map pp_var_name m.mstep.step_inputs in
        let output = List.map pp_var_name m.mstep.step_outputs in
        let args =
          (if is_machine_statefull m then [[pp_old pp_state_name;pp_state_name]] else [])
            @(if input!=[] then [input] else [])
            @(if output!=[] then [output] else [])
        in
        let transition fmt = pp_call fmt (pp_transition_name, args) in
        match guarantees with
          | [] -> Some (false, [], [transition])
          | _ ->  Some (false, [], transition::(List.map pp_var guarantees))
      in
      fprintf fmt "%a%a%a@,@,%a;%t" (* %a;@, *)
        pp_ifstatefull pp_state_decl_and_reset
        
        (*Declare the step procedure*)
        (pp_procedure pp_step_procedure_name (build_pp_arg_step m) pp_contract_opt) AdaNoContent
        
        pp_ifstatefull (fun fmt -> fprintf fmt ";@,")
        
        (*Declare the transition predicate*)
        (pp_transition_predicate true typed_submachines) (m_spec_opt, m)
        
        (*Print the private section*)
        pp_private_section
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
