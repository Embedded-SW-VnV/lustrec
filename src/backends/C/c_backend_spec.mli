module HdrMod : C_backend_header.MODIFIERS_HDR

module SrcMod : C_backend_src.MODIFIERS_SRC

module MakefileMod : C_backend_makefile.MODIFIERS_MKF

module MainMod : C_backend_main.MODIFIERS_MAINSRC

val sanitize_machines :
  Machine_code_types.machine_t list -> Machine_code_types.machine_t list
