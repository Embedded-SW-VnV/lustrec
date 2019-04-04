open Format
open Misc_printer

type parameter_mode = AdaNoMode | AdaIn | AdaOut | AdaInOut

type kind_def = AdaType | AdaProcedure | AdaFunction | AdaPackageDecl | AdaPackageBody

type visibility = AdaNoVisibility | AdaPrivate | AdaLimitedPrivate

type ada_var_decl = parameter_mode*printer*printer

type ada_local_decl =
  | AdaLocalVar of ada_var_decl
  | AdaLocalPackage of (printer * printer * ((printer*printer) list))

type def_content =
  | AdaNoContent
  | AdaPackageContent of printer
  | AdaVisibilityDefinition of visibility
  | AdaProcedureContent of ((ada_local_decl list list) * (printer list))
  | AdaRecord of (ada_var_decl list list)
  | AdaPackageInstanciation of (printer * ((printer*printer) list))


val pp_clean_ada_identifier : formatter -> string -> unit
val pp_package_access : (printer*printer) -> printer
val pp_block : formatter -> printer list -> unit
val pp_oneline_comment : formatter -> string -> unit
val pp_with : visibility -> formatter -> printer -> unit
val pp_var_decl : ada_var_decl -> printer
val pp_call : formatter -> (printer*(printer list list)) -> unit

(* declaration printer *)
val pp_package : printer -> printer list -> bool -> formatter -> printer -> unit
val pp_package_instanciation : printer -> printer -> formatter -> (printer*printer) list -> unit
val pp_type_decl : printer -> visibility -> printer
val pp_record : printer -> formatter -> ada_var_decl list list -> unit
val pp_procedure : printer -> (ada_var_decl list list) -> printer option -> formatter -> def_content -> unit
(* Local function :

val pp_parameter_mode : formatter -> parameter_mode -> unit
val pp_kind_def : formatter -> kind_def -> unit
val pp_visibility : formatter -> visibility -> unit
val pp_var_decl_lists : formatter -> ada_var_decl list list -> unit
val pp_def_args : formatter -> ada_var_decl list list -> unit
val pp_def : formatter -> (kind_def*printer*(ada_var_decl list list)*(printer option)*def_content*(printer option)) -> unit
*)
