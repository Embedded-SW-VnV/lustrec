open Seal_slice
open Seal_extract
open Seal_utils

let active = ref false

(* Select the appropriate node, should have been inlined already and
   extract update/output functions. *)
let seal_run basename prog machines =
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
    | s -> s
  in
  let m = Machine_code_common.get_machine machines node_name in
  let nd = m.mname in
  (* Format.eprintf "Node %a@." Printers.pp_node nd; *)
  let mems = m.mmemory in
  (* Format.eprintf "Mems: %a@." (Utils.fprintf_list ~sep:"; " Printers.pp_var) mems; *)
  let msch = Utils.desome m.msch in
  (* Format.eprintf "graph: %a@." Causality.pp_dep_graph deps; *)
  let sliced_nd = slice_node mems msch nd in
  (* Format.eprintf "Sliced Node %a@." Printers.pp_node sliced_nd; *)
  report ~level:3 (fun fmt -> Format.fprintf fmt "Node sliced@.");
  let sw_init, sw_sys = node_as_switched_sys mems sliced_nd in
  let pp_res =
    (Utils.fprintf_list ~sep:"@ "
       (fun fmt (gel, up) ->
         Format.fprintf fmt "@[<v 2>[%a]:@ %a@]"
           (Utils.fprintf_list ~sep:"; "
              (fun fmt (e,b) ->
                if b then Printers.pp_expr fmt e
                else Format.fprintf fmt "not(%a)"
                       Printers.pp_expr e)) gel
           (Utils.fprintf_list ~sep:";@ "
              (fun fmt (id, e) ->
                Format.fprintf fmt "%s = @[<hov 0>%a@]"
                  id
                  Printers.pp_expr e)) up
    ))
  in
  report ~level:1 (
      fun fmt -> Format.fprintf fmt
                   "%i memories, %i init, %i step switch cases@."
                   (List.length mems)
                   (List.length sw_init)
                   (List.length sw_sys)
               
    );
  report ~level:1 (fun fmt ->
      Format.fprintf fmt "@[<v 0>@[<v 3>Init:@ %a@]@ "
        pp_res sw_init;
      Format.fprintf fmt "@[<v 3>Step:@ %a@]@]@ "
        pp_res sw_sys
    );
  

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
    
