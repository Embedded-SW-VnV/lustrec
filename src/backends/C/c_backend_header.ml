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
module Mpfr = Lustrec_mpfr

(********************************************************************************************)
(* Header Printing functions *)
(********************************************************************************************)

module type MODIFIERS_HDR = sig
  module GhostProto : MODIFIERS_GHOST_PROTO

  val pp_machine_decl_prefix : formatter -> machine_t -> unit

  val pp_predicates : formatter -> machine_t list -> unit

  val pp_import_arrow : formatter -> unit -> unit

  val pp_machine_alloc_decl : formatter -> machine_t -> unit
end

module EmptyMod = struct
  module GhostProto = EmptyGhostProto

  let pp_machine_decl_prefix _ _ = ()

  let pp_predicates _ _ = ()

  let pp_import_arrow fmt () =
    fprintf
      fmt
      "#include \"%s/arrow.h%s\""
      (Arrow.arrow_top_decl ()).top_decl_owner
      (if !Options.cpp then "pp" else "")

  let pp_machine_alloc_decl _ _ = ()
end

module Main =
functor
  (Mod : MODIFIERS_HDR)
  ->
  struct
    module Protos = Protos (Mod.GhostProto)

    let pp_import_standard fmt () =
      (* if Machine_types.has_machine_type () then *)
      fprintf
        fmt
        "#include <stdint.h>@,%a%a"
        (if !Options.mpfr then pp_print_endcut "#include <mpfr.h>"
        else pp_print_nothing)
        ()
        Mod.pp_import_arrow
        ()

    (* TODO: ACSL we do multiple things: - provide the semantics of the node as
       a predicate: function step and reset are associated to ACSL predicate -
       the node is associated to a refinement contract, wrt its ACSL sem - if
       the node is a regular node associated to a contract, print the contract
       as function contract. - do not print anything if this is a contract
       node *)
    let pp_machine_alloc_decl fmt m =
      Mod.pp_machine_decl_prefix fmt m;
      if not (fst (get_stateless_status m)) then
        if !Options.static_mem then
          (* Static allocation *)
          let macro = m, mk_attribute m, mk_instance m in
          fprintf
            fmt
            "%a@,%a@,%a"
            (fun x -> pp_static_declare_macro x)
            macro
            (fun x -> pp_static_link_macro x)
            macro
            (fun x -> pp_static_alloc_macro x)
            macro
        else
          (* Dynamic allocation *)
          fprintf
            fmt
            "extern %a;@,extern %a"
            pp_alloc_prototype
            (m.mname.node_id, m.mstatic)
            pp_dealloc_prototype
            m.mname.node_id

    let pp_machine_struct_top_decl_from_header fmt tdecl =
      let inode = imported_node_of_top tdecl in
      if not (inode.nodei_stateless || inode.nodei_iscontract) then
        (* Declare struct *)
        fprintf fmt "%a;" (pp_machine_memtype_name ~ghost:false) inode.nodei_id

    let pp_stateless_C_prototype fmt (name, inputs, outputs) =
      let output = match outputs with [ hd ] -> hd | _ -> assert false in
      fprintf
        fmt
        "%a %s %a"
        (fun x -> pp_basic_c_type ~pp_c_basic_type_desc x)
        output.var_type
        name
        (pp_print_parenthesized pp_c_decl_input_var)
        inputs

    let pp_machine_decl_top_decl_from_header fmt tdecl =
      let inode = imported_node_of_top tdecl in
      (*Mod.print_machine_decl_prefix fmt m;*)
      let prototype = inode.nodei_id, inode.nodei_inputs, inode.nodei_outputs in
      if not inode.nodei_iscontract then
        if inode.nodei_prototype = Some "C" then
          if inode.nodei_stateless then
            fprintf fmt "extern %a;" pp_stateless_C_prototype prototype
          else (
            (* TODO: raise proper error *)
            Format.eprintf
              "internal error: pp_machine_decl_top_decl_from_header";
            assert false)
        else if inode.nodei_stateless then
          fprintf fmt "extern %a;" Protos.pp_stateless_prototype prototype
        else
          let static_inputs =
            List.filter (fun v -> v.var_dec_const) inode.nodei_inputs
          in
          let used name =
            List.exists
              (fun v -> v.var_id = name)
              (inode.nodei_inputs @ inode.nodei_outputs)
          in
          let self = mk_new_name used "self" in
          let mem = mk_new_name used "mem" in
          let static_prototype = inode.nodei_id, static_inputs in
          fprintf
            fmt
            "extern %a;@,extern %a;@,extern %a;@,extern %a;@,extern %a;"
            (Protos.pp_set_reset_prototype self mem)
            static_prototype
            (Protos.pp_clear_reset_prototype self mem)
            static_prototype
            (Protos.pp_init_prototype self)
            static_prototype
            (Protos.pp_clear_prototype self)
            static_prototype
            (Protos.pp_step_prototype self mem)
            prototype

    let pp_const_top_decl fmt tdecl =
      let cdecl = const_of_top tdecl in
      fprintf
        fmt
        "extern %a;"
        (pp_c_type cdecl.const_id)
        (if
         !Options.mpfr
         && Types.(is_real_type (array_base_type cdecl.const_type))
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
      (* | Tydec_float -> fprintf fmt "float %s" var *)
      | Tydec_bool ->
        fprintf fmt "_Bool %s" var
      | Tydec_clock ty ->
        pp_c_type_decl filename cpt var fmt ty
      | Tydec_const c ->
        fprintf fmt "%s %s" c var
      | Tydec_array (d, ty) ->
        fprintf
          fmt
          "%a[%a]"
          (pp_c_type_decl filename cpt var)
          ty
          pp_c_dimension
          d
      | Tydec_enum tl ->
        incr cpt;
        fprintf
          fmt
          "enum _enum_%s_%d %a %s"
          (protect_filename filename)
          !cpt
          (pp_print_braced pp_print_string)
          (List.sort compare tl)
          var
      | Tydec_struct fl ->
        incr cpt;
        fprintf
          fmt
          "struct _struct_%s_%d %a %s"
          (protect_filename filename)
          !cpt
          (pp_print_braced ~pp_sep:pp_print_semicolon (fun fmt (label, tdesc) ->
               pp_c_type_decl filename cpt label fmt tdesc))
          fl
          var

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

    let reset_type_definitions, pp_type_definition_top_decl_from_header =
      let cpt_type = ref 0 in
      ( (fun () -> cpt_type := 0),
        fun filename fmt tdecl ->
          let typ = typedef_of_top tdecl in
          fprintf
            fmt
            "typedef %a;"
            (pp_c_type_decl filename cpt_type typ.tydef_id)
            typ.tydef_desc )

    (********************************************************************************************)
    (* MAIN Header Printing functions *)
    (********************************************************************************************)

    let pp_alloc_header header_fmt basename machines dependencies =
      (* Include once: start *)
      let machines' = List.filter (fun m -> not m.mis_contract) machines in
      let baseNAME = file_to_module_name basename in
      fprintf
        header_fmt
        "@[<v>%a@,\
         #ifndef _%s_alloc@,\
         #define _%s_alloc@,\
         @,\
         /* Import header from %s */@,\
         %a@,\
         @,\
         %a%a%a%a%a#endif@]@."
        (* Print the svn version number and the supported C standard (C90 or
           C99) *)
        pp_print_version
        ()
        baseNAME
        baseNAME
        (* Import the header *) basename
        pp_import_prototype
        {
          local = true;
          name = basename;
          content = [];
          is_stateful = true (* assuming it is staful *);
        }
        (* Print dependencies *)
        (pp_print_list
           ~pp_open_box:pp_open_vbox0
           ~pp_prologue:(pp_print_endcut "/* Import dependencies */")
           pp_import_alloc_prototype
           ~pp_epilogue:pp_print_cutcut)
        dependencies
        (* Print the struct definitions of all machines. *)
        (pp_print_list
           ~pp_open_box:pp_open_vbox0
           ~pp_prologue:(pp_print_endcut "/* Struct definitions */")
           ~pp_sep:pp_print_cutcut
           pp_machine_struct
           ~pp_epilogue:pp_print_cutcut)
        machines'
        (* Copy the spec (valid and memory packs predicates). *)
        Mod.pp_predicates
        machines
        (* Print the prototypes of all machines *)
        (pp_print_list
           ~pp_open_box:pp_open_vbox0
           ~pp_prologue:
             (pp_print_endcut "/* Node allocation function/macro prototypes */")
           ~pp_sep:pp_print_cutcut
           pp_machine_alloc_decl
           ~pp_epilogue:pp_print_cutcut)
        machines'
        (* Print the spec prototypes of all machines *)
        (pp_print_list
           ~pp_open_box:pp_open_vbox0
           ~pp_prologue:
             (pp_print_endcut
                "/* Node allocation function/macro ghost prototypes */")
           ~pp_sep:pp_print_cutcut
           Mod.pp_machine_alloc_decl
           ~pp_epilogue:pp_print_cutcut)
        machines'
    (* Include once: end *)

    (* Function called when compiling a lusi file and generating the associated
       C header. *)
    let pp_header_from_header header_fmt basename header =
      (* Include once: start *)
      let baseNAME = file_to_module_name basename in
      let types = get_typedefs header in
      let consts = get_consts header in
      let nodes = get_imported_nodes header in
      let dependencies = get_dependencies header in
      reset_type_definitions ();
      fprintf
        header_fmt
        "@[<v>%a@,\
         #ifndef _%s@,\
         #define _%s@,\
         @,\
         /* Import standard library */@,\
         %a@,\
         @,\
         %a%a%a%a%a%a#endif@]@."
        (* Print the version number and the supported C standard (C90 or C99) *)
        pp_print_version
        ()
        baseNAME
        baseNAME
        (* imports standard library definitions (arrow) *)
        pp_import_standard
        ()
        (* imports dependencies *)
        (pp_print_list
           ~pp_open_box:pp_open_vbox0
           ~pp_prologue:(pp_print_endcut "/* Import dependencies */")
           (fun fmt dep ->
             let local, name = dependency_of_top dep in
             pp_import_prototype
               fmt
               {
                 local;
                 name;
                 content = [];
                 is_stateful = true (* assuming it is stateful *);
               })
           ~pp_epilogue:pp_print_cutcut)
        dependencies
        (* Print the type definitions from the type table *)
        (pp_print_list
           ~pp_open_box:pp_open_vbox0
           ~pp_prologue:(pp_print_endcut "/* Types definitions */")
           (pp_type_definition_top_decl_from_header basename)
           ~pp_epilogue:pp_print_cutcut)
        types
        (* Print the global constant declarations. *)
        (pp_print_list
           ~pp_open_box:pp_open_vbox0
           ~pp_prologue:
             (pp_print_endcut
                "/* Global constants (declarations, definitions are in C file) \
                 */")
           pp_const_top_decl
           ~pp_epilogue:pp_print_cutcut)
        consts
        (* MPFR *)
        (if !Options.mpfr then fun fmt () ->
         fprintf
           fmt
           "/* Global initialization declaration */@,\
            extern %a;@,\
            @,\
            /* Global clear declaration */@,\
            extern %a;@,\
            @,"
           pp_global_init_prototype
           baseNAME
           pp_global_clear_prototype
           baseNAME
        else pp_print_nothing)
        ()
        (* Print the struct declarations of all machines. *)
        (pp_print_list
           ~pp_open_box:pp_open_vbox0
           ~pp_prologue:(pp_print_endcut "/* Struct declarations */")
           pp_machine_struct_top_decl_from_header
           ~pp_epilogue:pp_print_cutcut)
        nodes
        (* Print the prototypes of all machines *)
        (pp_print_list
           ~pp_open_box:pp_open_vbox0
           ~pp_prologue:(pp_print_endcut "/* Nodes declarations */")
           ~pp_sep:pp_print_cutcut
           pp_machine_decl_top_decl_from_header
           ~pp_epilogue:pp_print_cutcut)
        nodes
  end
(* Local Variables: *)
(* compile-command:"make -C ../../.." *)
(* End: *)
