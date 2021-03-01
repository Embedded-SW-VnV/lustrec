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

open Lustre_types
open Machine_code_types
open Machine_code_common
open Utils.Format
open C_backend_common
open Utils

module type MODIFIERS_MAINSRC = sig
end

module EmptyMod = struct
end

module Main = functor (Mod: MODIFIERS_MAINSRC) -> struct

  (********************************************************************************************)
  (*                         Main related functions                                           *)
  (********************************************************************************************)

  let pp_c_main_var_input fmt id =
    fprintf fmt "%s" id.var_id

  let pp_c_main_var_output fmt id =
    if Types.is_address_type id.var_type
    then
      fprintf fmt "%s" id.var_id
    else
      fprintf fmt "&%s" id.var_id

  let print_put_output fmt id o' o =
    let suff = string_of_int (id + 1) in
    print_put_var fmt suff o'.var_id o.var_type o.var_id

  let print_main_inout_declaration fmt m =
    fprintf fmt
      "/* Declaration of inputs/outputs variables */@,\
       %a%a\
       @[<v 2>if (traces) {@,\
       %a%a@]@,\
       }"
      (pp_print_list_i
         ~pp_open_box:pp_open_vbox0
         ~pp_epilogue:pp_print_cut
         (fun fmt idx v ->
            fprintf fmt "%a; %a"
              (pp_c_type v.var_id) v.var_type
              (fun fmt () -> pp_file_decl fmt "in" idx) ())) m.mstep.step_inputs
      (pp_print_list_i
         ~pp_open_box:pp_open_vbox0
         ~pp_epilogue:pp_print_cut
         (fun fmt idx v ->
            fprintf fmt "%a; %a"
              (pp_c_type v.var_id) v.var_type
              (fun fmt () -> pp_file_decl fmt "out" idx) ())) m.mstep.step_outputs
      (pp_print_list_i
         ~pp_epilogue:pp_print_cut
         (fun fmt idx _ ->
            ignore (pp_file_open fmt "in" idx))) m.mstep.step_inputs
      (pp_print_list_i
         (fun fmt idx _ ->
            ignore (pp_file_open fmt "out" idx))) m.mstep.step_outputs

  let print_main_memory_allocation mname main_mem fmt m =
    if not (fst (get_stateless_status m)) then
      fprintf fmt
        "@[<v>/* Main memory allocation */@,\
         %a@,\
         @,\
         /* Initialize the main memory */@,\
         %a(%s);@]"
        (fun fmt () ->
           if !Options.static_mem && !Options.main_node <> "" then
             fprintf fmt "%a(static,main_mem);"
               pp_machine_static_alloc_name mname
           else
             fprintf fmt "%a *main_mem = %a();"
               (pp_machine_memtype_name ~ghost:false) mname
               pp_machine_alloc_name mname) ()
        pp_machine_reset_name mname
        main_mem

  let print_global_initialize fmt basename =
    let mNAME = file_to_module_name basename in
    fprintf fmt "/* Initialize global constants */@,%a();"
      pp_global_init_name mNAME

  let print_global_clear fmt basename =
    let mNAME = file_to_module_name basename in
    fprintf fmt "/* Clear global constants */@,%a();"
      pp_global_clear_name mNAME

  let print_main_initialize mname main_mem fmt m =
    let inputs = mpfr_vars m.mstep.step_inputs in
    let outputs = mpfr_vars m.mstep.step_outputs in
    if not (fst (get_stateless_status m))
    then
      fprintf fmt
        "/* Initialize inputs, outputs and memories */@,\
         %a%a%a(%s);"
        (pp_print_list
           ~pp_open_box:pp_open_vbox0
           ~pp_eol:pp_print_cut
           (pp_initialize m main_mem (pp_c_var_read m))) inputs
        (pp_print_list
           ~pp_open_box:pp_open_vbox0
           ~pp_eol:pp_print_cut
           (pp_initialize m main_mem (pp_c_var_read m))) outputs
        pp_machine_init_name mname
        main_mem
    else
      fprintf fmt
        "/* Initialize inputs and outputs */@,\
         %a%a@ "
        (pp_print_list
           ~pp_open_box:pp_open_vbox0
           ~pp_eol:pp_print_cut
           (pp_initialize m main_mem (pp_c_var_read m))) inputs
        (pp_print_list
           ~pp_open_box:pp_open_vbox0
           (pp_initialize m main_mem (pp_c_var_read m))) outputs

  let print_main_clear mname main_mem fmt m =
    let inputs = mpfr_vars m.mstep.step_inputs in
    let outputs = mpfr_vars m.mstep.step_outputs in
    if not (fst (get_stateless_status m))
    then
      fprintf fmt
        "@[<v>/* Clear inputs, outputs and memories */@,\
         %a%a%a(%s);@]"
        (pp_print_list
           ~pp_open_box:pp_open_vbox0
           ~pp_eol:pp_print_cut
           (pp_clear m main_mem (pp_c_var_read m))) inputs
        (pp_print_list
           ~pp_open_box:pp_open_vbox0
           ~pp_eol:pp_print_cut
           (pp_clear m main_mem (pp_c_var_read m))) outputs
        pp_machine_clear_name mname
        main_mem
    else
      fprintf fmt
        "@[<v>/* Clear inputs and outputs */@,\
         %a%a@]"
        (pp_print_list
           ~pp_open_box:pp_open_vbox0
           ~pp_eol:pp_print_cut
           (pp_clear m main_mem (pp_c_var_read m))) inputs
        (pp_print_list
           ~pp_open_box:pp_open_vbox0
           (pp_clear m main_mem (pp_c_var_read m))) outputs

let print_get_input fmt id v' v =
  let pp_file = pp_print_file ("in" ^ string_of_int (id + 1)) in
  let unclocked_t = Types.unclock_type v.var_type in
  fprintf fmt "@[<v>%a@]"
    (fun fmt () ->
       if Types.is_int_type unclocked_t then
         fprintf fmt "%s = _get_int(\"%s\");@,%a"
           v.var_id v'.var_id
           pp_file ("d", v.var_id)
       else if Types.is_bool_type unclocked_t then
         fprintf fmt "%s = _get_bool(\"%s\");@,%a"
           v.var_id v'.var_id
           pp_file ("i", v.var_id)
       else if Types.is_real_type unclocked_t then
         if !Options.mpfr then
           fprintf fmt "double %s_tmp = _get_double(\"%s\");@,\
                        %a@,\
                        mpfr_set_d(%s, %s_tmp, %i);"
             v.var_id v'.var_id
             pp_file ("f", v.var_id ^ "_tmp")
             v.var_id v.var_id (Mpfr.mpfr_prec ())
         else
           fprintf fmt "%s = _get_double(\"%s\");@,%a"
             v.var_id v'.var_id
             pp_file ("f", v.var_id)
       else begin
         Global.main_node := !Options.main_node;
         eprintf "Code generation error: %a%a@."
           Error.pp_error_msg Error.Main_wrong_kind
           Location.pp_loc v'.var_loc;
         raise (Error.Error (v'.var_loc, Error.Main_wrong_kind))
       end) ()

let pp_main_call mname self fmt m (inputs: value_t list) (outputs: var_decl list) =
  if fst (Machine_code_common.get_stateless_status m)
  then
    fprintf fmt "%a (%a%a);"
      pp_machine_step_name mname
      (pp_print_list ~pp_sep:pp_print_comma ~pp_eol:pp_print_comma
         (pp_c_val m self pp_c_main_var_input)) inputs
      (pp_print_list ~pp_sep:pp_print_comma pp_c_main_var_output) outputs
  else
    fprintf fmt "%a (%a%a%s);"
      pp_machine_step_name mname
      (pp_print_list ~pp_sep:pp_print_comma ~pp_eol:pp_print_comma
         (pp_c_val m self pp_c_main_var_input)) inputs
      (pp_print_list ~pp_sep:pp_print_comma ~pp_eol:pp_print_comma
         pp_c_main_var_output) outputs
      self

  let print_main_loop mname main_mem fmt m =
    let input_values = List.map (fun v ->
        mk_val (Var v) v.var_type) m.mstep.step_inputs in
    fprintf fmt
      "ISATTY = isatty(0);@,\
       @,\
       /* Infinite loop */@,\
       @[<v 2>while(1){@,\
       fflush(stdout);@,\
       @[<v 2>if (traces) {@,\
       %a%a\
       @]@,\
       }@,\
       %a%a%a"

      (pp_print_list_i
        ~pp_open_box:pp_open_vbox0
        ~pp_epilogue:pp_print_cut
         (fun fmt idx _ -> fprintf fmt "fflush(f_in%i);" (idx + 1)))
      m.mstep.step_inputs

      (pp_print_list_i
        ~pp_open_box:pp_open_vbox0
         (fun fmt idx _ -> fprintf fmt "fflush(f_out%i);" (idx + 1)))
      m.mstep.step_outputs

      (pp_print_list_i2
        ~pp_open_box:pp_open_vbox0
        ~pp_epilogue:pp_print_cut
         print_get_input)
      (m.mname.node_inputs, m.mstep.step_inputs)

      (fun fmt () ->
         pp_main_call mname main_mem fmt m input_values m.mstep.step_outputs) ()

      (pp_print_list_i2
         ~pp_open_box:pp_open_vbox0
         ~pp_prologue:pp_print_cut
         print_put_output)
      (m.mname.node_outputs, m.mstep.step_outputs)

  let print_usage fmt () =
    fprintf fmt
      "@[<v 2>\
       void usage(char *argv[]) {@,\
       printf(\"Usage: %%s\\n\", argv[0]);@,\
       printf(\" -t: produce trace files for input/output flows\\n\");@,\
       printf(\" -d<dir>: directory containing traces (default: _traces)\\n\");@,\
       printf(\" -p<prefix>: prefix_simu.scope<id> (default: file_node)\\n\");@,\
       exit (8);@]@,\
       }"

  let print_options fmt name =
    fprintf fmt
      "@[<v>int traces = 0;@,\
       char* prefix = \"%s\";@,\
       char* dir = \".\";@,\
       @[<v 2>while ((argc > 1) && (argv[1][0] == '-')) {@,\
       @[<v 2>switch (argv[1][1]) {@,\
       @[<v 2>case 't':@,\
       traces = 1;@,\
       break;@,\
       @]@,\
       @[<v 2>case 'd':@,\
       dir = &argv[1][2];@,\
       break;@,\
       @]@,\
       @[<v 2>case 'p':@,\
       prefix = &argv[1][2];@,\
       break;@,\
       @]@,\
       @[<v 2>default:@,\
       printf(\"Wrong Argument: %%s\\n\", argv[1]);@,\
       usage(argv);@]@]@,\
       }@,\
       ++argv;@,\
       --argc;@]@,\
       }@]"
      name

  let print_main_code fmt (basename, m) =
    let mname = m.mname.node_id in
    (* TODO: find a proper way to shorthen long names. This causes segfault in the binary when trying to fprintf in them *)
    let mname = if String.length mname > 50
      then string_of_int (Hashtbl.hash mname) else mname in
    let main_mem =
      if !Options.static_mem && !Options.main_node <> ""
      then "&main_mem"
      else "main_mem" in

    fprintf fmt
      "@[<v>\
       %a@,\
       @,\
       @[<v 2>int main (int argc, char *argv[]) {@,\
       %a@,\
       @,\
       %a@,\
       %a@,\
       %a@,\
       %a@,\
       %a@,\
       %a@]@,\
       }@,\
       %areturn 1;@]@,}@]@."

      print_usage ()

      print_options (basename ^ "_" ^ mname)

      print_main_inout_declaration m

      (Plugins.c_backend_main_loop_body_prefix basename mname) ()

      (print_main_memory_allocation mname main_mem) m

      (fun fmt () ->
         if !Options.mpfr then
           fprintf fmt "@[<v>%a@,%a@]@,"
             print_global_initialize basename
             (print_main_initialize mname main_mem) m) ()

      (print_main_loop mname main_mem) m

      Plugins.c_backend_main_loop_body_suffix ()

      (fun fmt () ->
         if !Options.mpfr then
           fprintf fmt "@[<v>%a@,%a@]@,"
             (print_main_clear mname main_mem) m
             print_global_clear basename) ()

  let print_main_header fmt () =
    fprintf fmt
      "@[<v>#include <stdio.h>@,\
       #include <unistd.h>@,\
       %a@]"
      (fun fmt () -> fprintf fmt
          (if !Options.cpp then
             "#include \"%s/io_frontend.hpp\""
           else
             "#include <string.h>@,\
              #include \"%s/io_frontend.h\"")
          (Options_management.core_dependency "io_frontend")) ()

  let print_main_c main_fmt main_machine basename _prog _machines _dependencies =
    fprintf main_fmt
      "@[<v>\
       %a@,\
       #include <stdlib.h>@,\
       #include <assert.h>@,\
       %a@,\
       @,\
       %a@,\
       %a
       @]@."
      print_main_header ()
      print_import_alloc_prototype
      {
        local = true;
        name = basename;
        content = [];
        is_stateful = true (* assuming it is stateful*)
      }

      (* Print the svn version number and the supported C standard (C90 or C99) *)
      pp_print_version ()

      print_main_code (basename, main_machine)

end

(* Local Variables: *)
(* compile-command:"make -C ../../.." *)
(* End: *)
