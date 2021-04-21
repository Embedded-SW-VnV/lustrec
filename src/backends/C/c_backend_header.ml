(********************************************************************)
(*                                                                  *)
(*  The LustreC compiler toolset   /  The LustreC Development Team  *)
(*  Copyright 2012 -    --   ONERA - CNRS - INPT                    *)
(*                                                                  *)
(*  LustreC is free software, distributed WITHOUT ANY WARRANTY      *)
(*  under the terms of the GNU Lesser General Public License        *)
(*  version 2.1.                                                    *)
(*                                                                  *)
(********************************************************************)

open Utils.Format
open Lustre_types
open Corelang
open Machine_code_types
open Machine_code_common
open C_backend_common

(********************************************************************************************)
(*                         Header Printing functions                                        *)
(********************************************************************************************)


module type MODIFIERS_HDR = sig
  val print_machine_decl_prefix: Format.formatter -> machine_t -> unit
  val pp_import_standard_spec: formatter -> unit -> unit
end

module EmptyMod = struct
  let print_machine_decl_prefix = fun _ _ -> ()
  let pp_import_standard_spec _ _ = ()
end

module Main = functor (Mod: MODIFIERS_HDR) -> struct

  let print_import_standard fmt () =
    (* if Machine_types.has_machine_type () then *)
    fprintf fmt
      "#include <stdint.h>@,\
       %a\
       #include \"%s/arrow.h%s\"\
       %a"
      (if !Options.mpfr then
         pp_print_endcut "#include <mpfr.h>"
       else pp_print_nothing) ()
      (Arrow.arrow_top_decl ()).top_decl_owner
      (if !Options.cpp then "pp" else "")
      Mod.pp_import_standard_spec ()

  let rec print_static_val pp_var fmt v =
    match v.value_desc with
    | Cst c ->
      pp_c_const fmt c
    | Var v ->
      pp_var fmt v
    | Fun (n, vl) ->
      pp_basic_lib_fun (Types.is_int_type v.value_type) n
        (print_static_val pp_var) fmt vl
    | _ ->
      (* TODO: raise proper error *)
      eprintf "Internal error: C_backend_header.print_static_val";
      assert false

  let print_constant_decl (m, attr, inst) pp_var fmt v =
    fprintf fmt "%s %a = %a"
      attr
      (pp_c_type (sprintf "%s ## %s" inst v.var_id)) v.var_type
      (print_static_val pp_var) (get_const_assign m v)

  let pp_var inst const_locals fmt v =
    if List.mem v const_locals then
      fprintf fmt "%s ## %s" inst v.var_id
    else fprintf fmt "%s" v.var_id

  let print_static_constant_decl (_, _, inst as macro) fmt const_locals =
    pp_print_list ~pp_open_box:pp_open_vbox0
      ~pp_sep:(pp_print_endcut ";\\")  ~pp_eol:(pp_print_endcut ";\\")
      (print_constant_decl macro (pp_var inst const_locals))
      fmt
      const_locals

  let print_static_declare_instance
      (m, attr, inst) const_locals fmt (i, (n, static)) =
    let values = List.map (value_of_dimension m) static in
    fprintf fmt "%a(%s, %a%s)"
      pp_machine_static_declare_name (node_name n)
      attr
      (pp_print_list ~pp_open_box:pp_open_hbox ~pp_sep:pp_print_comma
         ~pp_eol:pp_print_comma (print_static_val (pp_var inst const_locals)))
      values
      i

  let print_static_declare_macro fmt (m, attr, inst as macro) =
    let const_locals =
      List.filter (fun vdecl -> vdecl.var_dec_const) m.mstep.step_locals in
    let array_mem =
      List.filter (fun v -> Types.is_array_type v.var_type) m.mmemory in
    fprintf fmt
      "@[<v 2>\
       #define %a(%s, %a%s)\\@,\
       %a%s %a %s;\\@,\
       %a%a;\
       @]"
      pp_machine_static_declare_name m.mname.node_id
      attr
      (pp_print_list ~pp_sep:pp_print_comma ~pp_eol:pp_print_comma
         (pp_c_var_read m)) m.mstatic
      inst
      (* constants *)
      (print_static_constant_decl macro) const_locals
      attr
      (pp_machine_memtype_name ~ghost:false) m.mname.node_id
      inst
      (pp_print_list ~pp_open_box:pp_open_vbox0
         ~pp_sep:(pp_print_endcut ";\\") ~pp_eol:(pp_print_endcut ";\\")
         (pp_c_decl_local_var m)) array_mem
      (pp_print_list ~pp_open_box:pp_open_vbox0
         ~pp_sep:(pp_print_endcut ";\\")
         (fun fmt (i', m') ->
            let path = sprintf "%s ## _%s" inst i' in
            fprintf fmt "%a"
              (print_static_declare_instance macro const_locals)
              (path, m'))) m.minstances

  let print_static_link_instance fmt (i, (m, _)) =
    fprintf fmt "%a(%s)" pp_machine_static_link_name (node_name m) i

  (* Allocation of a node struct:
     - if node memory is an array/matrix/etc, we cast it to a pointer (see pp_registers_struct)
  *)
  let print_static_link_macro fmt (m, _, inst) =
    let array_mem = List.filter (fun v -> Types.is_array_type v.var_type)
        m.mmemory in
    fprintf fmt
      "@[<v>@[<v 2>\
       #define %a(%s) do {\\@,\
       %a%a;\\@]@,\
       } while (0)\
       @]"
      pp_machine_static_link_name m.mname.node_id
      inst
      (pp_print_list ~pp_open_box:pp_open_vbox0
         ~pp_sep:(pp_print_endcut ";\\") ~pp_eol:(pp_print_endcut ";\\")
         (fun fmt v ->
            fprintf fmt "%s._reg.%s = (%a*) &%s"
              inst
              v.var_id
              (fun fmt v -> pp_c_type "" fmt (Types.array_base_type v.var_type)) v
              v.var_id)) array_mem
      (pp_print_list ~pp_open_box:pp_open_vbox0
         ~pp_sep:(pp_print_endcut ";\\")
         (fun fmt (i',m') ->
            let path = sprintf "%s ## _%s" inst i' in
            fprintf fmt "%a;\\@,%s.%s = &%s"
              print_static_link_instance (path,m')
              inst
              i'
              path)) m.minstances

  let print_static_alloc_macro fmt (m, attr, inst) =
    fprintf fmt
      "@[<v>@[<v 2>\
       #define %a(%s, %a%s)\\@,\
       %a(%s, %a%s);\\@,\
       %a(%s);\
       @]@]"
      pp_machine_static_alloc_name m.mname.node_id
      attr
      (pp_print_list ~pp_sep:pp_print_comma ~pp_eol:pp_print_comma
         (pp_c_var_read m)) m.mstatic
      inst
      pp_machine_static_declare_name m.mname.node_id
      attr
      (pp_print_list ~pp_sep:pp_print_comma ~pp_eol:pp_print_comma
         (pp_c_var_read m)) m.mstatic
      inst
      pp_machine_static_link_name m.mname.node_id
      inst

  (* TODO: ACSL
     we do multiple things:
     - provide the semantics of the node as a predicate: function step and reset are associated to ACSL predicate
     - the node is associated to a refinement contract, wrt its ACSL sem
     - if the node is a regular node associated to a contract, print the contract as function contract.
     - do not print anything if this is a contract node
  *)
  let print_machine_alloc_decl fmt m =
    Mod.print_machine_decl_prefix fmt m;
    if not (fst (get_stateless_status m)) then
      if !Options.static_mem then
        (* Static allocation *)
        let macro = (m, mk_attribute m, mk_instance m) in
        fprintf fmt "%a@,%a@,%a"
          print_static_declare_macro macro
          print_static_link_macro macro
          print_static_alloc_macro macro
      else
        (* Dynamic allocation *)
        fprintf fmt "extern %a;@,extern %a"
          print_alloc_prototype (m.mname.node_id, m.mstatic)
          print_dealloc_prototype m.mname.node_id

  let print_machine_struct_top_decl_from_header fmt tdecl =
    let inode = imported_node_of_top tdecl in
    if not inode.nodei_stateless then
      (* Declare struct *)
      fprintf fmt "%a;"
        (pp_machine_memtype_name ~ghost:false) inode.nodei_id

  let print_stateless_C_prototype fmt (name, inputs, outputs) =
    let output =
      match outputs with
      | [hd] -> hd
      | _ -> assert false
    in
    fprintf fmt "%a %s %a"
      (pp_basic_c_type ~pp_c_basic_type_desc ~var_opt:None) output.var_type
      name
      (pp_print_parenthesized pp_c_decl_input_var) inputs

  let print_machine_decl_top_decl_from_header fmt tdecl =
    let inode = imported_node_of_top tdecl in
    (*Mod.print_machine_decl_prefix fmt m;*)
    let prototype = (inode.nodei_id, inode.nodei_inputs, inode.nodei_outputs) in
    if inode.nodei_prototype = Some "C" then
      if inode.nodei_stateless then
        fprintf fmt "extern %a;" print_stateless_C_prototype prototype
      else begin
        (* TODO: raise proper error *)
        Format.eprintf "internal error: print_machine_decl_top_decl_from_header";
        assert false
      end
    else if inode.nodei_stateless then
      fprintf fmt "extern %a;" print_stateless_prototype prototype
    else
      let static_inputs = List.filter (fun v -> v.var_dec_const)
          inode.nodei_inputs in
      let used name =
        List.exists (fun v -> v.var_id = name)
          (inode.nodei_inputs @ inode.nodei_outputs) in
      let self = mk_new_name used "self" in
      let static_prototype = (inode.nodei_id, static_inputs) in
      fprintf fmt
        "extern %a;@,\
         extern %a;@,\
         extern %a;@,\
         extern %a;"
        (print_reset_prototype self) static_prototype
        (print_init_prototype self) static_prototype
        (print_clear_prototype self) static_prototype
        (print_step_prototype self) prototype

  let print_const_top_decl fmt tdecl =
    let cdecl = const_of_top tdecl in
    fprintf fmt "extern %a;"
      (pp_c_type cdecl.const_id)
      (if !Options.mpfr && Types.(is_real_type (array_base_type cdecl.const_type))
       then Types.dynamic_type cdecl.const_type
       else cdecl.const_type)

  let rec pp_c_type_decl filename cpt var fmt tdecl =
    match tdecl with
    | Tydec_any ->
      assert false
    | Tydec_int ->
      fprintf fmt "int %s" var
    | Tydec_real when !Options.mpfr ->
      fprintf fmt "%s %s" Mpfr.mpfr_t var
    | Tydec_real ->
      fprintf fmt "double %s" var
    (* | Tydec_float         -> fprintf fmt "float %s" var *)
    | Tydec_bool ->
      fprintf fmt "_Bool %s" var
    | Tydec_clock ty ->
      pp_c_type_decl filename cpt var fmt ty
    | Tydec_const c ->
      fprintf fmt "%s %s" c var
    | Tydec_array (d, ty) ->
      fprintf fmt "%a[%a]" (pp_c_type_decl filename cpt var) ty pp_c_dimension d
    | Tydec_enum tl ->
      incr cpt;
      fprintf fmt "enum _enum_%s_%d %a %s" (protect_filename filename) !cpt
        (pp_print_braced pp_print_string) tl var
    | Tydec_struct fl ->
      incr cpt;
      fprintf fmt "struct _struct_%s_%d %a %s" (protect_filename filename) !cpt
        (pp_print_braced ~pp_sep:pp_print_semicolon
           (fun fmt (label, tdesc) -> pp_c_type_decl filename cpt label fmt tdesc))
        fl var

  (* let print_type_definitions fmt filename =
   *   let cpt_type = ref 0 in
   *   Hashtbl.iter (fun typ decl ->
   *       match typ with
   *       | Tydec_const var ->
   *         begin match decl.top_decl_desc with
   *           | TypeDef tdef ->
   *             fprintf fmt "typedef %a;@.@."
   *               (pp_c_type_decl filename cpt_type var) tdef.tydef_desc
   *           | _ -> assert false
   *         end
   *       | _ -> ()) type_table *)

  let reset_type_definitions, print_type_definition_top_decl_from_header =
    let cpt_type = ref 0 in
    (fun () -> cpt_type := 0),
    (fun filename fmt tdecl ->
       let typ = typedef_of_top tdecl in
       fprintf fmt "typedef %a;"
         (pp_c_type_decl filename cpt_type typ.tydef_id) typ.tydef_desc)

  (********************************************************************************************)
  (*                         MAIN Header Printing functions                                   *)
  (********************************************************************************************)

  let print_alloc_header header_fmt basename _prog machines dependencies spec =
    (* Include once: start *)
    let baseNAME = file_to_module_name basename in
    fprintf header_fmt
      "@[<v>\
       %a@,\
       #ifndef _%s_alloc@,\
       #define _%s_alloc@,\
       @,\
       /* Import header from %s */@,\
       %a@,\
       @,\
       %a\
       %a\
       %a\
       #endif\
       @]"

      (* Print the svn version number and the supported C standard (C90 or C99) *)
      pp_print_version ()

      baseNAME baseNAME

      (* Import the header *)
      basename
      print_import_prototype
      {
        local = true;
        name = basename;
        content = [];
        is_stateful = true  (* assuming it is staful *);
      }

      (* Print dependencies *)
      (pp_print_list
         ~pp_open_box:pp_open_vbox0
         ~pp_prologue:(pp_print_endcut "/* Import dependencies */")
         print_import_alloc_prototype
         ~pp_epilogue:pp_print_cutcut) dependencies

      (* Print the struct definitions of all machines. *)
      (pp_print_list
         ~pp_open_box:pp_open_vbox0
         ~pp_prologue:(pp_print_endcut "/* Struct definitions */")
         ~pp_sep:pp_print_cutcut
         print_machine_struct
         ~pp_epilogue:pp_print_cutcut) machines

      (* Print the prototypes of all machines *)
      (pp_print_list
         ~pp_open_box:pp_open_vbox0
         ~pp_prologue:(pp_print_endcut
                         "/* Node allocation function/macro prototypes */")
         ~pp_sep:pp_print_cutcut
         print_machine_alloc_decl
         ~pp_epilogue:pp_print_cutcut) machines
  (* Include once: end *)

  (* Function called when compiling a lusi file and generating the associated C
     header. *)
  let print_header_from_header header_fmt basename header =
    (* Include once: start *)
    let baseNAME = file_to_module_name basename in
    let types = get_typedefs header in
    let consts = get_consts header in
    let nodes = get_imported_nodes header in
    let dependencies = get_dependencies header in
    reset_type_definitions ();
    fprintf header_fmt
      "@[<v>\
       %a@,\
       #ifndef _%s@,\
       #define _%s@,\
       @,\
       /* Import standard library */@,\
       %a@,\
       @,\
       %a\
       %a\
       %a\
       %a\
       %a\
       %a\
       #endif\
       @]@."

      (* Print the version number and the supported C standard (C90 or C99) *)
      pp_print_version ()

      baseNAME baseNAME

      (* imports standard library definitions (arrow) *)
      print_import_standard ()

      (* imports dependencies *)
      (pp_print_list
         ~pp_open_box:pp_open_vbox0
         ~pp_prologue:(pp_print_endcut "/* Import dependencies */")
         (fun fmt dep ->
            let local, name = dependency_of_top dep in
            print_import_prototype fmt
              {
                local;
                name;
                content = [];
                is_stateful = true (* assuming it is stateful *)
              })
         ~pp_epilogue:pp_print_cutcut)
      dependencies

      (* Print the type definitions from the type table *)
      (pp_print_list
         ~pp_open_box:pp_open_vbox0
         ~pp_prologue:(pp_print_endcut "/* Types definitions */")
         (print_type_definition_top_decl_from_header basename)
         ~pp_epilogue:pp_print_cutcut)
      types

      (* Print the global constant declarations. *)
      (pp_print_list
         ~pp_open_box:pp_open_vbox0
         ~pp_prologue:
           (pp_print_endcut
              "/* Global constants (declarations, definitions are in C file) */")
         print_const_top_decl
         ~pp_epilogue:pp_print_cutcut)
      consts

      (* MPFR *)
      (if !Options.mpfr then
         fun fmt () -> fprintf fmt
             "/* Global initialization declaration */@,\
              extern %a;@,@,\
              /* Global clear declaration */@,\
              extern %a;@,@,"
             print_global_init_prototype baseNAME
             print_global_clear_prototype baseNAME
       else pp_print_nothing) ()

      (* Print the struct declarations of all machines. *)
      (pp_print_list
         ~pp_open_box:pp_open_vbox0
         ~pp_prologue:(pp_print_endcut "/* Struct declarations */")
         print_machine_struct_top_decl_from_header
         ~pp_epilogue:pp_print_cutcut)
      nodes

      (* Print the prototypes of all machines *)
      (pp_print_list
         ~pp_open_box:pp_open_vbox0
         ~pp_prologue:(pp_print_endcut "/* Nodes declarations */")
         ~pp_sep:pp_print_cutcut
         print_machine_decl_top_decl_from_header
         ~pp_epilogue:pp_print_cutcut)
      nodes

end
(* Local Variables: *)
(* compile-command:"make -C ../../.." *)
(* End: *)
