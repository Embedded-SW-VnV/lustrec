val kind2_print : bool ref

val mpfr : bool ref

val print_dec_types : bool ref

val verbose_level : int ref

val main_node : string ref

val global_inline : bool ref

val mpfr_prec : int ref

type option_spec = SpecNo | SpecACSL | SpecC

val spec : option_spec ref

type option_output = OutC | OutAda | OutJava | OutEMF | OutHorn | OutLustre
(* | OutACSL *)

val output : option_output ref

val pp_output : Format.formatter -> unit

val ansi : bool ref

val int_type : string ref

val real_type : string ref

val optimization : int ref

val include_dirs : string list ref

val dest_dir : string ref

val print_types : bool ref

val print_clocks : bool ref

val print_nodes : bool ref

val print_prec_double : int ref

val solve_al : bool ref

val al_nb_max : int ref

val delay_calculus : bool ref

val static_mem : bool ref

val check : bool ref

val lusi : bool ref

val traces : bool ref

val horn_cex : bool ref

val horn_query : bool ref

val sfunction : string ref

val print_reuse : bool ref

val const_unfold : bool ref

val witnesses : bool ref

val cpp : bool ref

val integer_div_euclidean : bool ref

val mauve : string ref

val nb_mutants : int ref

val gen_mcdc : bool ref

val no_mutation_suffix : bool ref

val compile_header : bool ref

val track_exceptions : bool ref

val c_main_options : bool ref

val compile_contracts : bool ref
