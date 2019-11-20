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

  let rec init f = function i when i < 0 -> [] | i -> (f i)::(init f (i-1)) (*should be replaced by the init of list from ocaml std lib*)

  let suffixOld = "_old"
  let suffixNew = "_new"
  let pp_invariant_name fmt = fprintf fmt "inv"
  let pp_transition_name fmt = fprintf fmt "transition"
  let pp_init_name fmt = fprintf fmt "init"
  let pp_state_name_predicate suffix fmt = fprintf fmt "%t%s" pp_state_name suffix
  let pp_axiomatize_package_name fmt = fprintf  fmt "axiomatize"

  (** Print the expression function representing the transition predicate.
     @param fmt the formater to print on
     @param machine the machine
  **)
  let pp_init_predicate typed_submachines fmt (opt_spec_machine, m) =
    let new_state = (AdaIn, pp_state_name_predicate suffixNew, pp_state_type, None) in
    pp_predicate pp_init_name [[new_state]] true fmt None

  (** Print the expression function representing the transition predicate.
     @param fmt the formater to print on
     @param machine the machine
  **)
  let pp_transition_predicate typed_submachines fmt (opt_spec_machine, m) =
    let old_state = (AdaIn, pp_state_name_predicate suffixOld, pp_state_type, None) in
    let new_state = (AdaIn, pp_state_name_predicate suffixNew, pp_state_type, None) in
    let inputs = build_pp_var_decl_step_input AdaIn None m in
    let outputs = build_pp_var_decl_step_output AdaIn None m in
    pp_predicate pp_transition_name ([[old_state; new_state]]@inputs@outputs) true fmt None

  let pp_invariant_predicate typed_submachines fmt (opt_spec_machine, m) =
    pp_predicate pp_invariant_name [[build_pp_state_decl AdaIn None]] true fmt None

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

    let memories = match m_spec_opt with
      | None -> []
      | Some m -> List.map (fun x-> pp_var_decl (build_pp_var_decl AdaNoMode (Some (true, false, [], [])) x)) m.mmemory
    in
    let ghost_private = memories in
    (* Commented since not used. Could be reinjected in the code 
    let vars_spec = match m_spec_opt with
      | None -> []
      | Some m_spec -> List.map (build_pp_var_decl AdaNoMode (Some (true, false, [], []))) (m_spec.mmemory)
    in *)
    let vars = List.map (build_pp_var_decl AdaNoMode None) m.mmemory in
    let states = List.map (build_pp_state_decl_from_subinstance AdaNoMode None) typed_instances in
    let var_lists =
      (if states = [] then [] else [states]) @
      (if vars = [] then [] else [vars]) in
    
    let pp_ifstatefull fmt pp =
      if is_machine_statefull m then
        fprintf fmt "%t" pp
      else
        fprintf fmt ""
    in

    let pp_state_decl_and_reset fmt =
      let init fmt = pp_call fmt (pp_access pp_axiomatize_package_name pp_init_name, [[pp_state_name]]) in
      let contract = Some (false, false, [], [init]) in
      fprintf fmt "%t;@,@,%a;@,@,"
        (*Declare the state type*)
        (pp_type_decl pp_state_type AdaPrivate)
        
        (*Declare the reset procedure*)
        (pp_procedure pp_reset_procedure_name (build_pp_arg_reset m) contract) AdaNoContent
    in

    let pp_private_section fmt =
      fprintf fmt "@,private@,@,%a%t%a%t%a"
      (*Instantiate the polymorphic type that need to be instantiated*)
      (Utils.fprintf_list ~sep:";@," pp_new_package) typed_machines_to_instanciate
      (Utils.pp_final_char_if_non_empty ";@,@," typed_machines_to_instanciate)
      
      (*Define the state type*)
      pp_ifstatefull (fun fmt-> pp_record pp_state_type fmt var_lists)
        
      (Utils.pp_final_char_if_non_empty ";@,@," ghost_private)
      (Utils.fprintf_list ~sep:";@," (fun fmt pp -> pp fmt)) ghost_private
    in

    let pp_content fmt =
      let pp_contract_opt =
        let pp_var x fmt =
            pp_clean_ada_identifier fmt x
        in
        let guarantee_post_conditions = List.map pp_var guarantees in
        let state_pre_conditions, state_post_conditions =
          if is_machine_statefull m then
          begin
            let input = List.map pp_var_name m.mstep.step_inputs in
            let output = List.map pp_var_name m.mstep.step_outputs in
            let args =
              [[pp_old pp_state_name;pp_state_name]]
                @(if input!=[] then [input] else [])
                @(if output!=[] then [output] else [])
            in
            let transition fmt = pp_call fmt (pp_access pp_axiomatize_package_name pp_transition_name, args) in
            let invariant fmt = pp_call fmt (pp_access pp_axiomatize_package_name pp_invariant_name, [[pp_state_name]]) in
            [invariant], [transition;invariant]
          end
          else
            [], []
        in
        let post_conditions = state_post_conditions@guarantee_post_conditions in
        let pre_conditions = state_pre_conditions in
        if post_conditions = [] && pre_conditions = [] then
          None
        else
          Some (false, false, pre_conditions, post_conditions)
      in
      let pp_guarantee name = pp_var_decl (AdaNoMode, (fun fmt -> pp_clean_ada_identifier fmt name), pp_boolean_type , (Some (true, false, [], []))) in
      let ghost_public = List.map pp_guarantee guarantees in
      fprintf fmt "@,%a%t%a%a%a@,@,%a;@,@,%t"
        
        (Utils.fprintf_list ~sep:";@," (fun fmt pp -> pp fmt)) ghost_public
        (Utils.pp_final_char_if_non_empty ";@,@," ghost_public)
        
        pp_ifstatefull pp_state_decl_and_reset
        
        (*Declare the step procedure*)
        (pp_procedure pp_step_procedure_name (build_pp_arg_step m) pp_contract_opt) AdaNoContent
        
        pp_ifstatefull (fun fmt -> fprintf fmt ";@,")
        
        (pp_package (pp_axiomatize_package_name) [] false)
          (fun fmt -> fprintf fmt "pragma Annotate (GNATProve, External_Axiomatization);@,@,%a;@,%a;@,%a"
            (*Declare the init predicate*)
            (pp_init_predicate typed_submachines) (m_spec_opt, m)
            (*Declare the transition predicate*)
            (pp_transition_predicate typed_submachines) (m_spec_opt, m)
            (*Declare the invariant predicate*)
            (pp_invariant_predicate typed_submachines) (m_spec_opt, m)
          )
        
        (*Print the private section*)
        pp_private_section
    in
    
    let pp_poly_type id = pp_type_decl (pp_polymorphic_type id) AdaPrivate in
    let pp_generics = List.map pp_poly_type polymorphic_types in
    
    fprintf fmt "@[<v>%a%t%a;@]@."
      
      (* Include all the subinstance package*)
      (Utils.fprintf_list ~sep:";@," (pp_with AdaNoVisibility)) machines_to_import
      (Utils.pp_final_char_if_non_empty ";@,@," machines_to_import)
      
      (*Begin the package*)
      (pp_package (pp_package_name m) pp_generics false) pp_content

end
