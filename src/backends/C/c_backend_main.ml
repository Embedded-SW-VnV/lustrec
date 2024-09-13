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

open Utils
open Lustre_types
open Machine_code_types
open Machine_code_common
open Format
open C_backend_common
module Mpfr = Lustrec_mpfr

module type MODIFIERS_MAINSRC = sig
  val pp_declare_ghost_state : formatter -> ident -> unit

  val pp_ghost_state_parameter : formatter -> unit -> unit

  val pp_main_spec : formatter -> unit

  val pp_main_loop_invariants :
    ident -> machine_t list -> formatter -> machine_t -> unit
end

module EmptyMod = struct
  let pp_declare_ghost_state _ _ = ()

  let pp_ghost_state_parameter _ _ = ()

  let pp_main_spec _ = ()

  let pp_main_loop_invariants _ _ _ _ = ()
end

module Main (Mod : MODIFIERS_MAINSRC) = struct
  (********************************************************************************************)
  (* Main related functions *)
  (********************************************************************************************)

  let pp_c_main_var_input fmt id = fprintf fmt "%s" id.var_id

  let pp_c_main_var_output fmt id =
    if Types.is_address_type id.var_type then fprintf fmt "%s" id.var_id
    else fprintf fmt "&%s" id.var_id

  let pp_put_output fmt id o' o =
    let suff = string_of_int (id + 1) in
    pp_put_var fmt suff o'.var_id o.var_type o.var_id

  let pp_mkdir_log_folder fmt =
    fprintf fmt
      "char* mkdir_instr = malloc((strlen(dir)+10) * sizeof(char));@,\
       strcpy (mkdir_instr, \"mkdir -p \");@,\
       strcat(mkdir_instr, dir);@,\
       system(mkdir_instr);"
    
  let pp_main_inout_declaration fmt m =
    let opt = !Options.c_main_options in
    fprintf
      fmt
      "/* Declaration of inputs/outputs variables */@,%a%a%a"
      (pp_print_list_i ~pp_open_box:pp_open_vbox0 (fun fmt idx v ->
           fprintf
             fmt
             "%a; %a"
             (pp_c_type v.var_id)
             v.var_type
             (if opt then fun fmt () -> pp_file_decl fmt "in" idx
             else pp_print_nothing)
             ()))
      m.mstep.step_inputs
      (pp_print_list_i
         ~pp_open_box:pp_open_vbox0
         ~pp_prologue:pp_print_cut
         (fun fmt idx v ->
           fprintf
             fmt
             "%a; %a"
             (pp_c_type v.var_id)
             v.var_type
             (if opt then fun fmt () -> pp_file_decl fmt "out" idx
             else pp_print_nothing)
             ()))
      m.mstep.step_outputs
      (if opt then fun fmt () ->
       fprintf
         fmt
         "@,@[<v 2>if (traces) {@,%t@,%a%a@]@,}"
         pp_mkdir_log_folder
         (pp_print_list_i (fun fmt idx _ ->
              ignore (pp_file_open fmt "in" idx)))
         m.mstep.step_inputs
         (pp_print_list_i ~pp_epilogue:pp_print_cut (fun fmt idx _ ->
              ignore (pp_file_open fmt "out" idx)))
         m.mstep.step_outputs
      else pp_print_nothing)
      ()

  let pp_main_memory_allocation mname main_mem fmt m =
    if not (fst (get_stateless_status m)) then
      fprintf
        fmt
        "@[<v>/* Main memory allocation */@,\
         %a@,\
         %a@,\
         /* Initialize the main memory */@,\
         %a(%s)%a;@]"
        (fun fmt () ->
          if !Options.static_mem && !Options.main_node <> "" then
            fprintf
              fmt
              "%a(,main_mem);"
              (fun x -> pp_machine_static_alloc_name x)
              mname
          else
            fprintf
              fmt
              "%a *main_mem = %a();"
              (pp_machine_memtype_name ~ghost:false)
              mname
              pp_machine_alloc_name
              mname)
        ()
        Mod.pp_declare_ghost_state
        mname
        pp_machine_set_reset_name
        mname
        main_mem
        Mod.pp_ghost_state_parameter
        ()

  let pp_global_initialize fmt basename =
    let mNAME = file_to_module_name basename in
    fprintf
      fmt
      "/* Initialize global constants */@,%a();"
      pp_global_init_name
      mNAME

  let pp_global_clear fmt basename =
    let mNAME = file_to_module_name basename in
    fprintf fmt "/* Clear global constants */@,%a();" pp_global_clear_name mNAME

  let pp_main_initialize mname main_mem fmt m =
    let inputs = mpfr_vars m.mstep.step_inputs in
    let outputs = mpfr_vars m.mstep.step_outputs in
    if not (fst (get_stateless_status m)) then
      fprintf
        fmt
        "/* Initialize inputs, outputs and memories */@,%a%a%a(%s);"
        (pp_print_list
           ~pp_open_box:pp_open_vbox0
           ~pp_eol:pp_print_cut
           (pp_initialize m main_mem (pp_c_var_read m)))
        inputs
        (pp_print_list
           ~pp_open_box:pp_open_vbox0
           ~pp_eol:pp_print_cut
           (pp_initialize m main_mem (pp_c_var_read m)))
        outputs
        pp_machine_init_name
        mname
        main_mem
    else
      fprintf
        fmt
        "/* Initialize inputs and outputs */@,%a%a@ "
        (pp_print_list
           ~pp_open_box:pp_open_vbox0
           ~pp_eol:pp_print_cut
           (pp_initialize m main_mem (pp_c_var_read m)))
        inputs
        (pp_print_list
           ~pp_open_box:pp_open_vbox0
           (pp_initialize m main_mem (pp_c_var_read m)))
        outputs

  let pp_main_clear mname main_mem fmt m =
    let inputs = mpfr_vars m.mstep.step_inputs in
    let outputs = mpfr_vars m.mstep.step_outputs in
    if not (fst (get_stateless_status m)) then
      fprintf
        fmt
        "@[<v>/* Clear inputs, outputs and memories */@,%a%a%a(%s);@]"
        (pp_print_list
           ~pp_open_box:pp_open_vbox0
           ~pp_eol:pp_print_cut
           (pp_clear m main_mem (pp_c_var_read m)))
        inputs
        (pp_print_list
           ~pp_open_box:pp_open_vbox0
           ~pp_eol:pp_print_cut
           (pp_clear m main_mem (pp_c_var_read m)))
        outputs
        pp_machine_clear_name
        mname
        main_mem
    else
      fprintf
        fmt
        "@[<v>/* Clear inputs and outputs */@,%a%a@]"
        (pp_print_list
           ~pp_open_box:pp_open_vbox0
           ~pp_eol:pp_print_cut
           (pp_clear m main_mem (pp_c_var_read m)))
        inputs
        (pp_print_list
           ~pp_open_box:pp_open_vbox0
           (pp_clear m main_mem (pp_c_var_read m)))
        outputs

  let pp_get_input fmt id v' v =
    let opt = !Options.c_main_options in
    let pp_file fmt =
      if opt then fprintf fmt "@,%a" (pp_file ("in" ^ string_of_int (id + 1)))
      else pp_print_nothing fmt
    in
    let unclocked_t = Types.unclock_type v.var_type in
    fprintf
      fmt
      "@[<v>%a@]"
      (fun fmt () ->
        if Types.is_int_type unclocked_t then
          fprintf
            fmt
            "%s = _get_int(\"%s\");%a"
            v.var_id
            v'.var_id
            pp_file
            ("d", v.var_id)
        else if Types.is_bool_type unclocked_t then
          fprintf
            fmt
            "%s = _get_bool(\"%s\");%a"
            v.var_id
            v'.var_id
            pp_file
            ("i", v.var_id)
        else if Types.is_real_type unclocked_t then
          if !Options.mpfr then
            fprintf
              fmt
              "double %s_tmp = _get_double(\"%s\");%a@,\
               mpfr_set_d(%s, %s_tmp, %i);"
              v.var_id
              v'.var_id
              pp_file
              ("f", v.var_id ^ "_tmp")
              v.var_id
              v.var_id
              (Mpfr.mpfr_prec ())
          else
            fprintf
              fmt
              "%s = _get_double(\"%s\");%a"
              v.var_id
              v'.var_id
              pp_file
              ("f", v.var_id)
        else (
          Global.main_node := !Options.main_node;
          eprintf
            "Code generation error: %a%a@."
            Error.pp
            Error.Main_wrong_kind
            Location.pp
            v'.var_loc;
          raise (Error.Error (v'.var_loc, Error.Main_wrong_kind))))
      ()

  let pp_main_call mname self fmt m inputs outputs =
    let pp_inputs =
      pp_print_list
        ~pp_sep:pp_print_comma
        ~pp_eol:pp_print_comma
        (pp_c_val m self pp_c_main_var_input)
    in
    let pp_outputs ?pp_eol fmt x =
      pp_print_list ~pp_sep:pp_print_comma ?pp_eol pp_c_main_var_output fmt x
    in
    if fst (get_stateless_status m) then
      fprintf
        fmt
        "%a(%a%a);"
        pp_machine_step_name
        mname
        pp_inputs
        inputs
        (pp_outputs ~pp_eol:pp_print_nothing)
        outputs
    else
      fprintf
        fmt
        "%a(%a%a%s)%a;"
        pp_machine_step_name
        mname
        pp_inputs
        inputs
        (pp_outputs ~pp_eol:pp_print_comma)
        outputs
        self
        Mod.pp_ghost_state_parameter
        ()

  let pp_main_loop mname main_mem machines fmt m =
    let opt = !Options.c_main_options in
    let input_values =
      List.map (fun v -> mk_val (Var v) v.var_type) m.mstep.step_inputs
    in
    fprintf
      fmt
      "ISATTY = isatty(0);@,\
       @,\
       /* Infinite loop */@,\
       %a@[<v 2>while(1){@,\
       fflush(stdout);@,\
       %a%a%a%a%a@]@,\
       }"
      (Mod.pp_main_loop_invariants main_mem machines)
      m
      (if opt then fun fmt () ->
       fprintf
         fmt
         "@[<v 2>if (traces) {@,%a%a@]@,}@,"
         (pp_print_list_i
            ~pp_open_box:pp_open_vbox0
            ~pp_epilogue:pp_print_cut
            (fun fmt idx _ -> fprintf fmt "fflush(f_in%i);" (idx + 1)))
         m.mstep.step_inputs
         (pp_print_list_i ~pp_open_box:pp_open_vbox0 (fun fmt idx _ ->
              fprintf fmt "fflush(f_out%i);" (idx + 1)))
         m.mstep.step_outputs
      else pp_print_nothing)
      ()
      (pp_print_list_i2
         ~pp_open_box:pp_open_vbox0
         ~pp_epilogue:pp_print_cut
         pp_get_input)
      (m.mname.node_inputs, m.mstep.step_inputs)
      (fun fmt () ->
        pp_main_call mname main_mem fmt m input_values m.mstep.step_outputs)
      ()
      (pp_print_list_i2
         ~pp_open_box:pp_open_vbox0
         ~pp_prologue:pp_print_cut
         pp_put_output)
      (m.mname.node_outputs, m.mstep.step_outputs)
      Plugins.c_backend_main_loop_body_suffix
      ()


  let pp_usage fmt () =
    fprintf
      fmt
      "@[<v 2>void usage(char *argv[]) {@,\
       printf(\"Usage: %%s\\n\", argv[0]);@,\
       printf(\" -t: produce trace files for input/output flows\\n\");@,\
       printf(\" -d<dir>: directory containing traces (default: \
       _traces)\\n\");@,\
       printf(\" -p<prefix>: prefix_simu.scope<id> (default: file_node)\\n\");@,\
       exit (8);@]@,\
       }@,\
       @,"

  let pp_options fmt name =
    fprintf
      fmt
      "@[<v>int c;@,
       int traces = 0;@,\
       char* prefix = \"%s\";@,\
       char* dir = \"_traces\";@,\
       @[<v 2>while ((c = getopt(argc, argv, \"td:p:\")) != -1) {@,\
       @[<v 2>switch (c) {@,\
       @[<v 2>case 't':@,\
       traces = 1;@,\
       break;@,\
       @]@,\
       @[<v 2>case 'd':@,\
       dir = optarg;@,\
       break;@,\
       @]@,\
       @[<v 2>case 'p':@,\
       prefix = optarg;@,\
       break;@,\
       @]@,\
       @[<v 2>default:@,\
       printf(\"Wrong Argument: %%o\\n\", c);@,\
       usage(argv);@]@]@,\
       }@,\
       @]@,\
       }@]@,\
       @,"
      name

  let pp_main_code machines fmt (basename, m) =
    let opt = !Options.c_main_options in
    let mname = m.mname.node_id in
    (* TODO: find a proper way to shorthen long names. This causes segfault in
       the binary when trying to fprintf in them *)
    let mname =
      if String.length mname > 50 then string_of_int (Hashtbl.hash mname)
      else mname
    in
    let main_mem =
      if !Options.static_mem && !Options.main_node <> "" then "&main_mem"
      else "main_mem"
    in

    fprintf
      fmt
      "@[<v>%a%t@[<v 2>int main (%a) {@,\ 
       %a%a@,\ 
       %a@,\ 
       %a@,\ 
       %a@,\ 
       %a@,\ 
       %areturn 1;@]@,\ 
       }@]@."

      (* line 1: %a%t int main (%a) { *)
      (if opt then pp_usage else pp_print_nothing)
      ()
      Mod.pp_main_spec
      (if opt then pp_print_string else pp_print_nothing)
      "int argc, char *argv[]"

      (* line 2 %a%a *)
      (if opt then pp_options else pp_print_nothing)
      (basename ^ "_" ^ mname)
      pp_main_inout_declaration
      m

      (*line 3 *)
      (Plugins.c_backend_main_loop_body_prefix basename mname)
      ()
      
      (*line 4 *)
      (pp_main_memory_allocation mname main_mem)
      m
      
      (*line 5 *)
      (fun fmt () ->
        if !Options.mpfr then
          fprintf
            fmt
            "@[<v>%a@,%a@]@,"
            pp_global_initialize
            basename
            (pp_main_initialize mname main_mem)
            m)
      ()

      (* line 6: while loop *)
      (pp_main_loop mname main_mem machines)
      m

      (fun fmt () ->
        if !Options.mpfr then
          fprintf
            fmt
            "@[<v>%a@,%a@]@,"
            (pp_main_clear mname main_mem)
            m
            pp_global_clear
            basename)
      ()

  let pp_main_header fmt () =
    fprintf
      fmt
      "@[<v>#include <stdio.h>@,#include <unistd.h>@,%a@]"
      (fun fmt () ->
        fprintf
          fmt
          (if !Options.cpp then "#include \"%s/io_frontend.hpp\""
          else "#include <string.h>@,#include \"%s/io_frontend.h\"")
          (Options_management.core_dependency "io_frontend"))
      ()

  let pp_main_c main_fmt main_machine basename _prog machines _dependencies =
    fprintf
      main_fmt
      "@[<v>%a@,\
       #include <stdlib.h>@,\
       #include <assert.h>@,\
       %a@,\
       @,\
       %a@,\
       %a\n\
      \       @]@."
      pp_main_header
      ()
      pp_import_alloc_prototype
      {
        local = true;
        name = basename;
        content = [];
        is_stateful = true (* assuming it is stateful*);
      }
      (* Print the svn version number and the supported C standard (C90 or
         C99) *)
      pp_print_version
      ()
      (pp_main_code machines)
      (basename, main_machine)
end

(* Local Variables: *)
(* compile-command:"make -C ../../.." *)
(* End: *)
