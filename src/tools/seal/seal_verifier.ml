open Seal_slice
open Seal_extract
open Seal_utils

let active = ref false

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

  let consts = Corelang.(List.map const_of_top (get_consts prog)) in
  let sw_init, sw_sys, init_out, update_out = node_as_switched_sys consts mems sliced_nd in
  let pp_res pp_expr =
    (Utils.fprintf_list ~sep:"@ "
       (fun fmt (g, up) ->
         Format.fprintf fmt "@[<v 2>[%t]:@ %a@]"
           (fun fmt -> match g with None -> () | Some g -> pp_expr fmt g)
           
           (* (Utils.fprintf_list ~sep:"; "
            *    (fun fmt (e,b) ->
            *      if b then pp_expr fmt e
            *      else Format.fprintf fmt "not(%a)"
            *             pp_expr e)) gel *)
           (Utils.fprintf_list ~sep:";@ "
              (fun fmt (id, e) ->
                Format.fprintf fmt "%s = @[<hov 0>%a@]"
                  id
                  pp_expr e)) up
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
      (*let pp_res = pp_res (fun fmt e -> Format.fprintf fmt "%i" e.Lustre_types.expr_tag)  in*)
       let pp_res = pp_res Printers.pp_expr in
      Format.fprintf fmt "@[<v 0>@[<v 3>Init:@ %a@]@ "
        pp_res  sw_init;
      Format.fprintf fmt "@[<v 3>Step:@ %a@]@]@ "
        pp_res  sw_sys
    );
  let new_node = Seal_export.to_lustre m sw_init sw_sys init_out update_out in  
  Format.eprintf "%a@." Printers.pp_node new_node;
  let output_file = !Options.dest_dir ^ "/" ^ basename ^ "_seal.lus" in
  Format.eprintf "%s@." output_file;
  let new_top = Corelang.mktop_decl Location.dummy_loc output_file false (Node new_node) in

  let out = open_out output_file in
  let fmt = Format.formatter_of_out_channel out in
  Format.fprintf fmt "%a@." 
    Printers.pp_prog  (prog@[new_top]);
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
    
