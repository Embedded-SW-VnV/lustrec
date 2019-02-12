open Format

open Machine_code_types
open Lustre_types
open Corelang
open Machine_code_common

(** Print the name of a package associated to a machine.
   @param fmt the formater to print on
   @param machine the machine
*)
let pp_package_name fmt machine =
  fprintf fmt "%s" machine.mname.node_id


(** Print the ada package introduction sentence it can be used for body and
declaration. Boolean parameter body should be true if it is a body delcaration.
   @param fmt the formater to print on
   @param fmt the formater to print on
   @param machine the machine
*)
let pp_begin_package body fmt machine =
  fprintf fmt "package %s %a is"
    (if body then "body" else "")
    pp_package_name machine

(** Print the ada package conclusion sentence.
   @param fmt the formater to print on
   @param machine the machine
*)
let pp_end_package fmt machine =
  fprintf fmt "end %a;" pp_package_name machine
