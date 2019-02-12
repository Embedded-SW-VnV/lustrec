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

module Main =
struct

let pp_package_name fmt machine =
  fprintf fmt "%s" machine.mname.node_id

let pp_var_name fmt id =
  fprintf fmt "var_name"

let pp_var_type fmt id = fprintf fmt "var_type"
(*)  (match id.var_type.tdesc with
    | Types.Tbasic Types.Basic.Tint -> "int"
    | Types.Tbasic Types.Basic.Treal -> "double"
    | Types.Tbasic Types.Basic.Tbool -> "bool"
    | Types.Tbasic _ -> eprintf "Basic type error : %a@." Types.print_ty id.var_type; assert false (*TODO*)
    | _ -> eprintf "Type error : %a@." Types.print_ty id.var_type; assert false (*TODO*)
  )*)

(*
  if Types.is_array_type id.var_type
  then pp_c_type (sprintf "(*%s)" id.var_id) fmt (Types.array_base_type id.var_type)
  else pp_c_type                  id.var_id  fmt id.var_type
*)

let pp_begin_package fmt machine =
  fprintf fmt "package %a is" pp_package_name machine
let pp_end_package fmt machine =
  fprintf fmt "end %a;" pp_package_name machine
let pp_var_decl fmt id =
  fprintf fmt "type %a is %a;"
    pp_var_name id
    pp_var_type id

let print fmt machine =
  fprintf fmt "@[<v 2>%a@,%a@]@,%a@."
    pp_begin_package machine
    (Utils.fprintf_list ~sep:"@," pp_var_decl) machine.mmemory
    pp_end_package machine

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
