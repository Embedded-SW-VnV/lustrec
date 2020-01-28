
let active = ref false
let tiny_debug = ref false

    
let tiny_run ~basename prog machines =
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
  
   Format.printf "%a@." Tiny.Ast.fprint_stm ast; 

  ()
  
  
module Verifier =
  (struct
    include VerifierType.Default
    let name = "tiny"
    let options =
      [
        "-debug", Arg.Set tiny_debug, "tiny debug"
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
    
