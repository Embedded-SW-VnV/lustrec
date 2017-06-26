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

let version = Version.number
let codename = Version.codename
let include_dirs = ref ["."]

let main_node = ref ""
let static_mem = ref true
let print_types = ref true
let print_clocks = ref true
let delay_calculus = ref true
let track_exceptions = ref true
let ansi = ref false
let check = ref false
let spec = ref "acsl"
let output = ref "C"
let dest_dir = ref "."
let verbose_level = ref 1
let global_inline = ref false
let witnesses = ref false
let optimization = ref 2
let lusi = ref false
let print_reuse = ref false
let const_unfold = ref false
let mpfr = ref false
let mpfr_prec = ref 0

let traces = ref false
let horn_cex = ref false
let horn_query = ref true

let cpp       = ref false
let int_type  = ref "int"
let real_type = ref "double"
let print_prec_double = ref 15
let print_prec_float = ref 10

let sfunction = ref ""

let mauve = ref ""
(* test generation options *)
let nb_mutants = ref 1000
let gen_mcdc = ref false
let no_mutation_suffix = ref false



(* Local Variables: *)
(* compile-command:"make -C .." *)
(* End: *)
