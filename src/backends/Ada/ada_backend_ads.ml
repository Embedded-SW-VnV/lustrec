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

module Main =
struct

(** Print the name of a variable.
   @param fmt the formater to print on
   @param id the variable
*)
let pp_var_name fmt id =
  fprintf fmt "%s" id.var_id

(** Print the type of a variable.
   @param fmt the formater to print on
   @param id the variable
*)
let pp_var_type fmt id = fprintf fmt
  (match (Types.repr id.var_type).Types.tdesc with
    | Types.Tbasic Types.Basic.Tint -> "int"
    | Types.Tbasic Types.Basic.Treal -> "double"
    | Types.Tbasic Types.Basic.Tbool -> "bool"
    | _ -> eprintf "Type error : %a@." Types.print_ty id.var_type; assert false (*TODO*)
  )

type prototype_modifiers = In | Out

(** Print a prototype_modifiers.
   @param fmt the formater to print on
   @param modifier the modifier
*)
let pp_prototype_modifiers fmt modifier =
  fprintf fmt "%s" (match modifier with
                     | In  -> "in"
                     | Out -> "out")

(** Print a variable declaration.
   @param fmt the formater to print on
   @param id the variable
*)
let pp_var_decl fmt id =
  fprintf fmt "type %a is %a;"
    pp_var_name id
    pp_var_type id

(** Print the parameter of a prototype, a list of modifier(eg. in or out)
  can be given to specify the type.
   @param modifiers list of the modifiers for this parameter
   @param fmt the formater to print on
   @param id the variable
*)
let pp_parameter modifiers fmt id =
  fprintf fmt "%a: %a %a"
    pp_var_name id
    (Utils.fprintf_list ~sep:"@ " pp_prototype_modifiers) modifiers
    pp_var_type id

(** Print the prototype of a procedure
   @param fmt the formater to print on
   @param name the name of the procedure
   @param input list of the input parameter of the procedure
   @param output list of the output parameter of the procedure
*)
let pp_simple_prototype fmt (name, input, output) =
  fprintf fmt "procedure %s(@[<v>@[%a%t%a@])@]"
    name
    (Utils.fprintf_list ~sep:",@ " (pp_parameter [In])) input
    (Utils.pp_final_char_if_non_empty ",@," input)
    (Utils.fprintf_list ~sep:",@ " (pp_parameter [Out])) output

(** Print the prototype of the init procedure of a machine.
   @param fmt the formater to print on
   @param m the machine
*)
let pp_init_prototype fmt m =
  pp_simple_prototype fmt ("init", m.mstatic, [])

(** Print the prototype of the step procedure of a machine.
   @param fmt the formater to print on
   @param m the machine
*)
let pp_step_prototype fmt m =
  pp_simple_prototype fmt ("step", m.mstep.step_inputs, m.mstep.step_outputs)

(** Print the prototype of the reset procedure of a machine.
   @param fmt the formater to print on
   @param m the machine
*)
let pp_reset_prototype fmt m =
  pp_simple_prototype fmt ("reset", m.mstatic, [])

(** Print the prototype of the clear procedure of a machine.
   @param fmt the formater to print on
   @param m the machine
*)
let pp_clear_prototype fmt m =
  pp_simple_prototype fmt ("clear", m.mstatic, [])

(** Print the package declaration(ads) of a lustre node.
   @param fmt the formater to print on
   @param machine the machine
*)
let print fmt machine =
  fprintf fmt "@[<v 2>%a;@,%a;@,%a;@,%a;@,%a;@]@,%a@."
    (pp_begin_package false) machine
    pp_init_prototype machine
    pp_step_prototype machine
    pp_reset_prototype machine
    pp_clear_prototype machine
    pp_end_package machine
    (*(Utils.fprintf_list ~sep:"@," pp_var_decl) machine.mmemory*)

end

(*
package Example is
     type Number is range 1 .. 11;
     procedure Print_and_Increment (j: in out Number);
end Example;

Package body (example.adb)

with Ada.Text_IO;
package body Example is

  i : Number := Number'First;

  procedure Print_and_Increment (j: in out Number) is

    function Next (k: in Number) return Number is
    begin
      return k + 1;
    end Next;

  begin
    Ada.Text_IO.Put_Line ( "The total is: " & Number'Image(j) );
    j := Next (j);
  end Print_and_Increment;

-- package initialization executed when the package is elaborated
begin
  while i < Number'Last loop
    Print_and_Increment (i);
  end loop;
end Example;
*)
