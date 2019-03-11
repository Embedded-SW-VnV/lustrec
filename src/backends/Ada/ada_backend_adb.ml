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

  (** Printing function for basic assignement [var_name := value;].

      @param fmt the formater to print on
      @param var_name the name of the variable
      @param value the value to be assigned
   **)
  let pp_basic_assign m fmt var_name value =
    fprintf fmt "%a := %a"
      (pp_access_var m) var_name
      (pp_value m) value

  (** Printing function for assignement. For the moment, only use
      [pp_basic_assign] function.

      @param pp_var pretty printer for variables
      @param fmt the formater to print on
      @param var_name the name of the variable
      @param value the value to be assigned
   **)
  let pp_assign m pp_var fmt var_name value = pp_basic_assign m

  (** Extract from a machine the instance corresponding to the identifier,
        assume that the identifier exists in the instances of the machine.

     @param identifier the instance identifier
     @param machine a machine
     @return the instance of machine.minstances corresponding to identifier
  **)
  let get_instance identifier typed_instances =
    try
      List.assoc identifier typed_instances
    with Not_found -> assert false

  (** Printing the reset function. call

      @param typed_instances list of all typed machine instances of this machine
      @param machine the current machine
      @param instance the considered instance
      @param fmt the formater to use
   **)
  let pp_machine_reset typed_instances (machine: machine_t) fmt identifier =
    let (substitution, submachine) = get_instance identifier typed_instances in
    fprintf fmt "%a.%t(%t.%s)"
      (pp_package_name_with_polymorphic substitution) submachine
      pp_reset_procedure_name
      pp_state_name
      identifier

  (** Printing function for instruction. See
      {!type:Machine_code_types.instr_t} for more details on
      machine types.

      @param typed_instances list of all typed machine instances of this machine
      @param machine the current machine
      @param fmt the formater to print on
      @param instr the instruction to print
   **)
  let pp_machine_instr typed_instances machine fmt instr =
    match get_instr_desc instr with
      (* no reset *)
      | MNoReset _ -> ()
      (* reset  *)
      | MReset ident ->
          pp_machine_reset typed_instances machine fmt ident
      | MLocalAssign (ident, value) ->
          pp_basic_assign machine fmt ident value
      | MStateAssign (ident, value) ->
          pp_basic_assign machine fmt ident value
      | MStep ([i0], i, vl) when Basic_library.is_internal_fun i
                                   (List.map (fun v -> v.value_type) vl) ->
          let value = mk_val (Fun (i, vl)) i0.var_type in
          pp_basic_assign machine fmt i0 value
      | MStep (il, i, vl) -> fprintf fmt "Null"
      (* pp_basic_instance_call m self fmt i vl il *)
      | MBranch (_, []) -> fprintf fmt "Null"

      (* (Format.eprintf "internal error: C_backend_src.pp_machine_instr %a@." (pp_instr m) instr; assert false) *)
      | MBranch (g, hl) -> fprintf fmt "Null"
      (* if let t = fst (List.hd hl) in t = tag_true || t = tag_false
       * then (\* boolean case, needs special treatment in C because truth value is not unique *\)
       *   (\* may disappear if we optimize code by replacing last branch test with default *\)
       *   let tl = try List.assoc tag_true  hl with Not_found -> [] in
       *   let el = try List.assoc tag_false hl with Not_found -> [] in
       *   pp_conditional dependencies m self fmt g tl el
       * else (\* enum type case *\)
       *   (\*let g_typ = Typing.type_const Location.dummy_loc (Const_tag (fst (List.hd hl))) in*\)
       *   fprintf fmt "@[<v 2>switch(%a) {@,%a@,}@]"
       *     (pp_c_val m self (pp_c_var_read m)) g
       *     (Utils.fprintf_list ~sep:"@," (pp_machine_branch dependencies m self)) hl *)
      | MComment s  ->
        let lines = String.split_on_char '\n' s in
        fprintf fmt "%a" (Utils.fprintf_list ~sep:"" pp_oneline_comment) lines

(** Print the definition of the step procedure from a machine.

   @param typed_instances list of all typed machine instances of this machine
   @param fmt the formater to print on
   @param machine the machine
**)
let pp_step_definition typed_instances fmt m = pp_procedure_definition
      pp_step_procedure_name
      (pp_step_prototype m)
      (pp_machine_var_decl NoMode)
      (pp_machine_instr typed_instances m)
      fmt
      (m.mstep.step_locals, m.mstep.step_instrs)

(** Print the definition of the reset procedure from a machine.

   @param typed_instances list of all typed machine instances of this machine
   @param fmt the formater to print on
   @param machine the machine
**)
let pp_reset_definition typed_instances fmt m = pp_procedure_definition
      pp_reset_procedure_name
      (pp_reset_prototype m)
      (pp_machine_var_decl NoMode)
      (pp_machine_instr typed_instances m)
      fmt
      ([], m.minit)

(** Print the package definition(ads) of a machine.
  It requires the list of all typed instance.
  A typed submachine instance is (ident, type_machine) with ident
  the instance name and typed_machine is (substitution, machine) with machine
  the machine associated to the instance and substitution the instanciation of
  all its polymorphic types.
   @param fmt the formater to print on
   @param typed_instances list of all typed machine instances of this machine
   @param m the machine
**)
let pp_file fmt (typed_instances, machine) =
  fprintf fmt "%a@,  @[<v>@,%a;@,@,%a;@,@]@,%a;@."
    (pp_begin_package true) machine (*Begin the package*)
    (pp_reset_definition typed_instances) machine (*Define the reset procedure*)
    (pp_step_definition typed_instances) machine (*Define the step procedure*)
    pp_end_package machine  (*End the package*)

end

(* Local Variables: *)
(* compile-command: "make -C ../../.." *)
(* End: *)
