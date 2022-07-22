(* TODO

   - build the output function: for the moment we slice the node with
   its memories, building the function updating the memory. We will
   need later the output function, using inputs and memories to
   compute the output. A way to do this would be to declared memories
   as input, remove their definitions, and slice the node with its
   outputs. This should clean up unnecessary internal variables and
   give us the output function.

   - compute the dimension of the node (nb of memories)

   - if the updates are all linear or affine, provide the update as a
   matrix rather then a polynomial. Check if this is simpler to do
   here or in matlab.

   - analyzes require bounds on inputs or sometimes target property 
   over states. These could be specified as node annotations: eg     
     - /seal/bounds/inputs/semialg/: (in1^4 + in2^3, 1) 
       to specify that the inputs are constrained by a semialgebraic 
       set (p,b) such as p(inputs) <= b
     - /seal/bounds/inputs/LMI/: (todo_describe_a_matrix) .... and so on. 
       To be defined depending on needs.
     - /seal/prop/semialg/: (x3 - x5, 2) -- if x3 - x5 <= 2 is 
       the property to prove
     
 *)


open Seal_slice
open Seal_extract
open Seal_utils

let active = ref false
let seal_export = ref None

let set_export s = match s with
  | "lustre" | "lus" | "m" | "matlab" -> seal_export := Some s
  | _ -> (Format.eprintf "Unrecognized seal export: %s@.@?" s; exit 1)
           
(* Select the appropriate node, should have been inlined already and
   extract update/output functions. *)
let seal_run ~basename prog machines =
  let node_name =
    match !Options.main_node with
    | "" -> (
      Format.eprintf "SEAL verifier requires a main node.@.";
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
  let nd = m.mname in
  let mems = m.mmemory in

  report ~level:1 (fun fmt -> Format.fprintf fmt "Node %s compiled: %i memories@." nd.node_id (List.length mems));

  (* Slicing node *)
  let msch = Utils.desome m.msch in
  let sliced_nd = slice_node (mems@nd.node_outputs) msch nd in
  report ~level:3 (fun fmt -> Format.fprintf fmt "Node sliced@.");
  report ~level:10 (fun fmt -> Format.fprintf fmt "Sliced Node %a@." Printers.pp_node sliced_nd);

  let consts = Corelang.(List.map const_of_top (get_consts prog)) in

  let pp_sys = pp_sys Printers.pp_expr in
  if List.length mems = 0 then
    begin (* A stateless node = a function ! *)
      
      let update_out = fun_as_switched_sys consts sliced_nd in

      report ~level:1 (fun fmt ->
          Format.fprintf fmt
            "Output (%i step switch cases):@ @[<v 0>%a@]@."
            (List.length update_out)
            pp_sys update_out
        );
      
      let _ = match !seal_export with
        | Some "lustre" | Some "lus" ->
           Seal_export.fun_to_lustre basename prog m update_out  
        | Some "matlab" | Some "m" -> assert false (* TODO *)
        | Some _ -> assert false 
        | None -> ()
      in
      ()
    end
  else
    begin (* A stateful node *)

      let sw_init, sw_sys, init_out, update_out = node_as_switched_sys consts mems sliced_nd in

      report ~level:1 (fun fmt ->
          Format.fprintf fmt
            "DynSys: (%i memories, %i init, %i step switch cases)@ @[<v 0>@[<v 3>Init:@ %a@]@ @[<v 3>Step:@ %a@]@]@."
            (List.length mems)
            (List.length sw_init)
            (List.length sw_sys)
            pp_sys  sw_init
            pp_sys  sw_sys
        );
      
      report ~level:1 (fun fmt ->
          Format.fprintf fmt
            "Output (%i init, %i step switch cases):@ @[<v 0>@[<v 3>Init:@ %a@]@ @[<v 3>Step:@ %a@]@]@."
            (List.length init_out)
            (List.length update_out)
            pp_sys  init_out
            pp_sys  update_out
        );
      
      let _ = match !seal_export with
        | Some "lustre" | Some "lus" ->
           Seal_export.node_to_lustre basename prog m sw_init sw_sys init_out update_out  
        | Some "matlab" | Some "m" -> assert false (* TODO *)
        | Some _ -> assert false 
        | None -> ()
      in
      ()
    end
  
module Verifier =
  (struct
    include VerifierType.Default
    let name = "seal"
    let options =
      [
        "-export", Arg.String set_export, "seal export option (lustre, matlab)";
        "-debug", Arg.Set seal_debug, "seal debug"

      ]
    let activate () =
      active := true;
      Options.global_inline := true;
      Options.optimization := 0;
      Options.const_unfold := true;
      ()
      
    let is_active () = !active
    let run = seal_run
            
            
  end: VerifierType.S)
    
