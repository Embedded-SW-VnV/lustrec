open Seal_utils

let active = ref false

(* Select the appropriate node, should have been inlined already and
   extract update/output functions. *)
let seal_run basename prog machines =
  let node_name =
    match !Options.main_node with
    | "" -> assert false
    | s -> s
  in
  let m = Machine_code_common.get_machine machines node_name in
  let nd = m.mname in
  Format.eprintf "Node %a@." Printers.pp_node nd; 
  let mems = m.mmemory in
  Format.eprintf "Mems: %a@." (Utils.fprintf_list ~sep:"; " Printers.pp_var) mems;
  let msch = Utils.desome m.msch in
  let deps = msch.Scheduling_type.dep_graph in
  Format.eprintf "graph: %a@." Causality.pp_dep_graph deps;
  let sliced_nd = slice_node mems deps nd in
  Format.eprintf "Node %a@." Printers.pp_node sliced_nd; 
  ()
  
module Verifier =
  (struct
    include VerifierType.Default
    let name = "seal"
    let options = []
    let activate () =
      active := true;
      Options.global_inline := true
      
    let is_active () = !active
    let run = seal_run
      
                    
  end: VerifierType.S)
    
