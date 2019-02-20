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

(** Functions printing the .ads file **)
module Main =
struct

(** Find a submachine step call in a list of instructions.
    @param ident submachine instance ident
    @param instr_list List of instruction sto search
    @return a list of pair containing input types and output types for each step call found
**)
let rec find_submachine_step_call ident instr_list =
  let search_instr instruction = 
    match instruction.instr_desc with
      | MStep (il, i, vl) when String.equal i ident -> [
        (List.map (function x-> x.var_type) il,
           List.map (function x-> x.value_type) vl)]
      | MBranch (_, l) -> List.flatten
          (List.map (function x, y -> find_submachine_step_call ident y) l)
      | _ -> []
  in
  List.flatten (List.map search_instr instr_list)

(** Check that two types are the same.
   @param t1 a type
   @param t2 an other type
   @param return true if the two types are Tbasic or Tunivar and equal
**)
let check_type_equal (t1:Types.type_expr) (t2:Types.type_expr) =
  match (Types.repr t1).Types.tdesc, (Types.repr t2).Types.tdesc with
    | Types.Tbasic x, Types.Tbasic y -> x = y
    | Types.Tunivar,  Types.Tunivar  -> t1.tid = t2.tid
    | _ -> assert false (* TODO *)

(** Extend a substitution to unify the two given types. Only the
  first type can be polymorphic.
    @param subsitution the base substitution
    @param type_poly the type which can be polymorphic
    @param typ the type to match type_poly with
**)
let unification (substituion:(int*Types.type_expr) list) ((type_poly:Types.type_expr), (typ:Types.type_expr)) =
  assert(not (is_Tunivar typ));
  (* If type_poly is polymorphic *)
  if is_Tunivar type_poly then
    (* If a subsitution exists for it *)
    if List.mem_assoc type_poly.tid substituion then
    begin
      (* We check that the type corresponding to type_poly in the subsitution
         match typ *)
      assert(check_type_equal (List.assoc type_poly.tid substituion) typ);
      (* We return the original substituion, it is already correct *)
      substituion
    end
    (* If type_poly is not in the subsitution *)
    else
      (* We add it to the substituion *)
      (type_poly.tid, typ)::substituion
  (* iftype_poly is not polymorphic *)
  else
  begin
    (* We check that type_poly and typ are the same *)
    assert(check_type_equal type_poly typ);
    (* We return the original substituion, it is already correct *)
    substituion
  end

(** Check that two calls are equal. A call is
  a pair of list of types, the inputs and the outputs.
   @param calls a list of pair of list of types
   @param return true if the two pairs are equal
**)
let check_call_equal (i1, o1) (i2, o2) =
  (List.for_all2 check_type_equal i1 i2)
    && (List.for_all2 check_type_equal i1 i2)

(** Check that all the elements of list of calls are equal to one.
  A call is a pair of list of types, the inputs and the outputs.
   @param call a pair of list of types
   @param calls a list of pair of list of types
   @param return true if all the elements are equal
**)
let check_calls call calls =
  List.for_all (check_call_equal call) calls

(** Extract from a subinstance that can have polymorphic type the instantiation
    of all its polymorphic type instanciation for a given machine.
   @param machine the machine which instantiate the subinstance
   @param submachine the machine corresponding to the subinstance
   @return the correspondance between polymorphic type id and their instantiation
**)
let get_substitution machine ident submachine =
  (* extract the calls to submachines from the machine *)
  let calls = find_submachine_step_call ident machine.mstep.step_instrs in
  (* extract the first call  *)
  let call = match calls with
              (* assume that there is always one call to a subinstance *)
              | []    -> assert(false)
              | h::t  -> h in
  (* assume that all the calls to a subinstance are using the same type *)
  assert(check_calls call calls);
  (* make a list of all types from input and output vars *)
  let call_types = (fst call)@(snd call) in
  (* extract all the input and output vars from the submachine *)
  let machine_vars = submachine.mstep.step_inputs@submachine.mstep.step_outputs in
  (* keep only the type of vars *)
  let machine_types = List.map (function x-> x.var_type) machine_vars in
  (* assume that there is the same numer of input and output in the submachine
      and the call *)
  assert (List.length machine_types = List.length call_types);
  (* Unify the two lists of types *)
  let substituion = List.fold_left unification [] (List.combine machine_types call_types) in
  (* Assume that our substitution match all the possible
       polymorphic type of the node *)
  let polymorphic_types = find_all_polymorphic_type submachine in
  assert (List.length polymorphic_types = List.length substituion);
  assert (List.for_all (function x->List.mem_assoc x substituion) polymorphic_types);
  substituion

(** Print the declaration of a state element of a subinstance of a machine.
   @param machine the machine
   @param fmt the formater to print on
   @param substitution correspondance between polymorphic type id and their instantiation
   @param ident the identifier of the subinstance
   @param submachine the submachine of the subinstance
**)
let pp_machine_subinstance_state_decl fmt (substitution, ident, submachine) =
  pp_node_state_decl substitution ident fmt submachine

(** Print the state record for a machine.
   @param fmt the formater to print on
   @param var_list list of all state var
   @param typed_submachines list of pairs of instantiated types and machine
**)
let pp_state_record_definition fmt (var_list, typed_submachines) =
  fprintf fmt "@,  @[<v>record@,  @[<v>%a%t%a%t@]@,end record@]"
    (Utils.fprintf_list ~sep:";@;" pp_machine_subinstance_state_decl)
    typed_submachines
    (Utils.pp_final_char_if_non_empty ";@," typed_submachines)
    (Utils.fprintf_list ~sep:";@;" (pp_machine_var_decl NoMode))
    var_list
    (Utils.pp_final_char_if_non_empty ";" var_list)

(** Print the declaration for polymorphic types.
   @param fmt the formater to print on
   @param polymorphic_types all the types to print
**)
let pp_generic fmt polymorphic_types =
  let pp_polymorphic_types =
    List.map (fun id fmt -> pp_polymorphic_type fmt id) polymorphic_types in
  if polymorphic_types != [] then
      fprintf fmt "generic@,  @[<v>%a;@]@,"
        (Utils.fprintf_list ~sep:";@," pp_private_limited_type_decl)
        pp_polymorphic_types
  else
    fprintf fmt ""

(** Extract from a machine list the one corresponding to the given instance.
   @param machines list of all machines
   @param instance instance of a machine
   @return the machine corresponding to hte given instance
**)
let get_machine machines instance =
    let id = (extract_node instance).node_id in
    List.find  (function m -> m.mname.node_id=id) machines

(** Print instanciation of a generic type in a new statement.
   @param fmt the formater to print on
   @param id id of the polymorphic type
   @param typ the new type
**)
let pp_generic_instanciation fmt (id, typ) =
  fprintf fmt "%a => %a" pp_polymorphic_type id pp_type typ

(** Print a new statement instantiating a generic package.
   @param fmt the formater to print on
   @param substitutions the instanciation substitution
   @param ident the name of the instance, useless in this function
   @param submachine the submachine to instanciate
**)
let pp_new_package fmt (substitutions, ident, submachine)=
  fprintf fmt "package %a is new %a @[<v>(%a)@]"
    (pp_package_name_with_polymorphic substitutions) submachine
    pp_package_name submachine
    (Utils.fprintf_list ~sep:",@," pp_generic_instanciation) substitutions


(** Print the package declaration(ads) of a machine.
   @param fmt the formater to print on
   @param m the machine
**)
let pp_file machines fmt m =
  let submachines = List.map (get_machine machines) m.minstances in
  let names = List.map fst m.minstances in
  let var_list = m.mmemory in
  let typed_submachines = List.map2
    (fun instance submachine ->
      let ident = (fst instance) in
      get_substitution m ident submachine, ident, submachine)
    m.minstances submachines in
  let pp_record fmt =
    pp_state_record_definition fmt (var_list, typed_submachines) in
  let typed_submachines_filtered =
    List.filter (function (l, _, _) -> l != []) typed_submachines in
  let polymorphic_types = find_all_polymorphic_type m in
  fprintf fmt "@[<v>%a%t%a%a@,  @[<v>@,%a;@,@,%t;@,@,%t;@,@,private@,@,%a%t%a;@,@]@,%a;@.@]"
    
    (* Include all the subinstance*)
    (Utils.fprintf_list ~sep:";@," pp_with_machine) submachines
    (Utils.pp_final_char_if_non_empty ";@,@," submachines)
    
    pp_generic polymorphic_types
    
    (*Begin the package*)
    (pp_begin_package false) m
    
    (*Declare the state type*)
    pp_private_limited_type_decl pp_state_type
    
    (*Declare the reset procedure*)
    (pp_reset_prototype m)
    
    (*Declare the step procedure*)
    (pp_step_prototype m)
    
    (*Instantiate the polymorphic type that need to be instantiate*)
    (Utils.fprintf_list ~sep:";@," pp_new_package) typed_submachines_filtered
    (Utils.pp_final_char_if_non_empty ";@,@," typed_submachines_filtered)
    
    (*Define the state type*)
    pp_type_decl (pp_state_type, pp_record)
    
    (*End the package*)
    pp_end_package m

end
