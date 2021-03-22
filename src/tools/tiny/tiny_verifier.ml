
let active = ref false
let tiny_debug = ref false
let tiny_help = ref false
let descending = ref 1
let unrolling = ref 0
let output = ref false

              
let quiet () = Tiny.Report.verbosity := 0
let report = Tiny_utils.report
               
let print_tiny_help () =
  let open Format in
  Format.eprintf "@[Tiny verifier plugin produces a simple imperative code \
          output for the provided main node, inlining all calls. This \
          code can then be analyzed using tiny analyzer options.@]";
  Format.eprintf "@.@?";
  flush stdout

  
let tiny_run ~basename prog machines =
  if !tiny_help then (
    let _ = print_tiny_help () in
    exit 0
  );
  let node_name =
    match !Options.main_node with
    | "" -> (
      Format.eprintf "Tiny verifier requires a main node.@.";
      Format.eprintf "@[<v 2>Available ones are:@ %a@]@.@?"
        (Utils.fprintf_list ~sep:"@ "
           (fun fmt m ->
             Format.fprintf fmt "%s" m.Machine_code_types.mname.node_id
           )
        )
        machines; 
      exit 1
    )
    | s -> ( (* should have been addessed before *)
      match Machine_code_common.get_machine_opt machines s with
      | None -> begin
          Global.main_node := s;
          Format.eprintf "Code generation error: %a@." Error.pp_error_msg Error.Main_not_found;
          raise (Error.Error (Location.dummy_loc, Error.Main_not_found))
        end
      | Some _ -> s
    )
  in
  let m = Machine_code_common.get_machine machines node_name in
  let env = (* We add each variables of the node the Tiny env *)
    Tiny_utils.machine_to_env m in
  let nd = m.mname in
  (* Building preamble with some bounds on inputs *)
  (* TODO: deal woth contracts, asserts, ... *)
  let bounds_inputs = [] in
  let ast = Tiny_utils.machine_to_ast bounds_inputs m in
  let mems = m.mmemory in
  if !output then (
    let destname = !Options.dest_dir ^ "/" ^ basename ^ "_" ^ node_name ^ ".tiny" in
    report ~level:2 (fun fmt -> Format.fprintf fmt "Exporting resulting tiny source as %s@ " destname);
    let out = open_out destname in
    let fmt = Format.formatter_of_out_channel out in
    Format.fprintf fmt "%a@." Tiny.Ast.Var.Set.pp env; 
    Format.fprintf fmt "%a@." Tiny.Ast.fprint_stm ast; 
    close_out out;
  
  
  );
  report ~level:1 (fun fmt -> Format.fprintf fmt "%a@." Tiny.Ast.fprint_stm ast); 
  
  let dom =
     let open Tiny.Load_domains in
     prepare_domains (List.map get_domain !domains)
   in
   let results = Tiny.Analyze.analyze dom !descending !unrolling env ast in
   let module Results = (val results: Tiny.Analyze.Results) in
   let module Dom = Results.Dom in
   let module PrintResults = Tiny.PrintResults.Make (Dom) in
   let m = Results.results in
   (* if !Tiny.Report.verbosity > 1 then *)
   report ~level:1 (PrintResults.print m env ast)
   (* no !output_file *);
        (* else PrintResults.print_invariants m ast !output_file *)

   ()
  
  
module Verifier =
  (struct
    include VerifierType.Default
    let name = "tiny"
    let options =
      [
        "-debug", Arg.Set tiny_debug, "tiny debug";
        ("-abstract-domain", Arg.String Tiny.Load_domains.decl_domain,
         "<domain>  Use abstract domain <domain> " ^ Tiny.Domains.available_domains_str);
        (* ("-a", Arg.String Tiny.Load_domains.decl_domain,
         *  "<domain>  Use abstract domain <domain> " ^ Tiny.Domains.available_domains_str); *)
        ("-param", Arg.String Tiny.Load_domains.set_param,
         "<p>  Send <p> to the abstract domain, syntax <dom>:<p> can be used \
          to target the (sub)domain <dom>");
        (* ("-p", Arg.String Tiny.Load_domains.set_param,
         *  "<p>  Send <p> to the abstract domain, syntax <dom>:<p> can be used \
         *   to target the (sub)domain <dom>"); *)
        ("-help-domain", Arg.String Tiny.Load_domains.help_domain,
         "<domain>  Print params of <domain>");
        (* ("-h", Arg.String Tiny.Load_domains.help_domain, "<domain>  Print params of <domain>"); *)
        (* ("--compile", Arg.Set compile_mode, " Compilation mode: compile to C");
      ("-c", Arg.Set compile_mode,             " Compilation mode: compile to C");*)
        
        ("-quiet", Arg.Unit quiet, " Quiet mode");
        (* ("-q", Arg.Unit quiet, " Quiet mode"); *)
        ("-verbose", Arg.Set_int Tiny.Report.verbosity,
         "<n>  Verbosity level (default is 1)");
        (* ("-v", Arg.Set_int Tiny.Report.verbosity, "<n>  Verbosity level (default is 1)"); *)
  (*      ("--output", Arg.String set_output_file,
         "<filename> Output results to file <filename> (default is \
          standard ouput)");
        ("-o", Arg.String set_output_file,
         "<filename>  Output results to file <filename> (default is standard ouput)");
   *)
        ("-descending", Arg.Set_int descending,
         "<n>  Perform <n> descending iterations after fixpoint of a loop \
          is reached (default is 1)");
        (* ("-d", Arg.Set_int descending,
         *  "<n>  Perform <n> descending iterations after fixpoint of a loop \
         * is reached (default is 1)"); *)
      ("-unrolling", Arg.Set_int unrolling,
       "<n>  Unroll loops <n> times before computing fixpoint (default is 0)");
      ("-output", Arg.Set output,
       "<n>  Export resulting tiny file as <name>_<mainnode>.tiny");
      (* (\* ("-u", Arg.Set_int unrolling,
       *  *  "<n>  Unroll loops <n> times before computing fixpoint (default is 0)"); *\) *)
       "-help", Arg.Set tiny_help, "tiny help and usage";
        
      
      ]
      
    let activate () =
      active := true;
      (* Options.global_inline := true;
       * Options.optimization := 0;
       * Options.const_unfold := true; *)
      ()
      
    let is_active () = !active
    let run = tiny_run
            
            
  end: VerifierType.S)
    
