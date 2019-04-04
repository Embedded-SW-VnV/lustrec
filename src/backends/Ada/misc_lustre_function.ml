
open Machine_code_types
open Lustre_types
(*
open Corelang
open Machine_code_common
*)

let is_machine_statefull m = m.mmemory != [] || m.mcalls != []

(** Return true if its the arrow machine
   @param machine the machine to test
*)
let is_arrow machine = String.equal Arrow.arrow_id machine.mname.node_id

(** Extract a node from an instance.
   @param instance the instance
**)
let extract_node instance =
  let (_, (node, _)) = instance in
  match node.top_decl_desc with
    | Node nd         -> nd
    | _ -> assert false (*TODO*)

(** Extract from a machine list the one corresponding to the given instance.
      assume that the machine is in the list.
   @param machines list of all machines
   @param instance instance of a machine
   @return the machine corresponding to hte given instance
**)
let get_machine machines instance =
    let id = (extract_node instance).node_id in
    try
      List.find (function m -> m.mname.node_id=id) machines
    with
      Not_found -> assert false (*TODO*)

(** Test if two types are the same.
   @param typ1 the first type
   @param typ2 the second type
**)
let pp_eq_type typ1 typ2 = 
  let get_basic typ = match (Types.repr typ).Types.tdesc with
    | Types.Tbasic Types.Basic.Tint -> Types.Basic.Tint
    | Types.Tbasic Types.Basic.Treal -> Types.Basic.Treal
    | Types.Tbasic Types.Basic.Tbool -> Types.Basic.Tbool
    | _ -> assert false (*TODO*)
  in
  get_basic typ1 = get_basic typ2

(** Extract all the inputs and outputs.
   @param machine the machine
   @return a list of all the var_decl of a macine
**)
let get_all_vars_machine m =
  m.mmemory@m.mstep.step_inputs@m.mstep.step_outputs@m.mstatic

(** Check if a type is polymorphic.
   @param typ the type
   @return true if its polymorphic
**)
let is_Tunivar typ = (Types.repr typ).tdesc == Types.Tunivar

(** Find all polymorphic type : Types.Tunivar in a machine.
   @param machine the machine
   @return a list of id corresponding to polymorphic type
**)
let find_all_polymorphic_type m =
  let vars = get_all_vars_machine m in
  let extract id = id.var_type.tid in
  let polymorphic_type_vars =
    List.filter (function x-> is_Tunivar x.var_type) vars in
  List.sort_uniq (-) (List.map extract polymorphic_type_vars)


(** Check if a submachine is statefull.
    @param submachine a submachine
    @return true if the submachine is statefull
**)
let is_submachine_statefull submachine =
    not (snd (snd submachine)).mname.node_dec_stateless

(** Find a submachine step call in a list of instructions.
    @param ident submachine instance ident
    @param instr_list List of instruction sto search
    @return a list of pair containing input types and output types for each step call found
**)
let rec find_submachine_step_call ident instr_list =
  let search_instr instruction = 
    match instruction.instr_desc with
      | MStep (il, i, vl) when String.equal i ident -> [
        (List.map (function x-> x.value_type) vl,
            List.map (function x-> x.var_type) il)]
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
let rec check_type_equal (t1:Types.type_expr) (t2:Types.type_expr) =
  match (Types.repr t1).Types.tdesc, (Types.repr t2).Types.tdesc with
    | Types.Tbasic x, Types.Tbasic y -> x = y
    | Types.Tunivar,  Types.Tunivar  -> t1.tid = t2.tid
    | Types.Ttuple l, _ -> assert (List.length l = 1); check_type_equal (List.hd l) t2
    | _, Types.Ttuple l -> assert (List.length l = 1); check_type_equal t1 (List.hd l)
    | Types.Tstatic (_, t), _ -> check_type_equal t t2
    | _, Types.Tstatic (_, t) -> check_type_equal t1 t
    | _ -> assert false

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
      (try
        assert(check_type_equal (List.assoc type_poly.tid substituion) typ)
      with
        Not_found -> assert false);
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
    of all its polymorphic type instanciation for a given machine. It searches
    the step calls and extract a substitution for all polymorphic type from
    it.
   @param machine the machine which instantiate the subinstance
   @param ident the identifier of the instance which permits to find the step call
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
  let substitution = List.fold_left unification [] (List.combine machine_types call_types) in
  (* Assume that our substitution match all the possible
       polymorphic type of the node *)
  let polymorphic_types = find_all_polymorphic_type submachine in
  assert (List.length polymorphic_types = List.length substitution);
  (try
    assert (List.for_all (fun x -> List.mem_assoc x substitution) polymorphic_types)
  with
    Not_found -> assert false);
  substitution


(** Extract from a machine the instance corresponding to the identifier,
      assume that the identifier exists in the instances of the machine.

   @param identifier the instance identifier
   @param machine a machine
   @return the instance of machine.minstances corresponding to identifier
**)
let get_instance identifier typed_submachines =
  try
    List.assoc identifier typed_submachines
  with Not_found -> assert false

