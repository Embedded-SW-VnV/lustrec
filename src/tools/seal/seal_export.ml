(* Multiple export channels for switched systems:
- lustre
- matlab
- text
 *)
open Lustre_types
open Machine_code_types
open Seal_utils

let verbose = true

let process_sw vars f_e sw =
  let process_branch g_opt up =
    let el = List.map (fun (v,e) -> v, f_e e) up in
    (* Sorting list of elements, according to vars, safety check to
         ensure that no variable is forgotten. *)
    let el, forgotten = List.fold_right (fun v (res, remaining) ->
                            let vid = v.var_id in
                            if List.mem_assoc vid remaining then
                              ((List.assoc vid remaining)::res),
                              (List.remove_assoc vid remaining)
                            else (
                              Format.eprintf
                                "Looking for variable %s in remaining expressions: [%a]@."
                                vid
                                (Utils.fprintf_list ~sep:";@ "
                                   (fun fmt (id,e) ->
                                     Format.fprintf fmt
                                       "(%s -> %a)"
                                       id
                                       Printers.pp_expr e))
                                remaining;
                              assert false (* Missing variable v in list *)
                            )
                          ) vars ([], el)
    in
    assert (forgotten = []);
    let loc = (List.hd el).expr_loc in
    let new_e = Corelang.mkexpr loc (Expr_tuple el) in
    match g_opt with
      None -> None, new_e, loc
    | Some g ->
       let g = f_e g in
       let ee = Corelang.mkeexpr loc g in
       let new_e = if verbose then
                     {new_e with
                       expr_annot =
                         Some ({annots = [["seal";"guards"],ee];
                                annot_loc = loc})} else new_e 
       in
       Some g, new_e, loc
  in
  let rec process_sw f_e sw = 
    match sw with
    | [] -> assert false
    | [g_opt,up] -> ((* last case, no need to guard it *)
      let _, up_e, _ = process_branch g_opt up in
      up_e
    )
    | (g_opt,up)::tl ->
       let g_opt, up_e, loc = process_branch g_opt up in
       match g_opt with
       | None -> (
         Format.eprintf "SEAL issue: process_sw with %a"
           pp_sys sw
       ;
         assert false (* How could this happen anyway ? *)
       )
       | Some g ->
          let tl_e = process_sw f_e tl in
          Corelang.mkexpr loc (Expr_ite (g, up_e, tl_e)) 
  in
  process_sw f_e sw

    
let sw_to_lustre m sw_init sw_step init_out update_out =
  let orig_nd = m.mname in
  let copy_nd = orig_nd (*Corelang.copy_node orig_nd *) in
  let vl = (* memories *)
    match sw_init with
    | [] -> assert false
    | (gl, up)::_ -> List.map (fun (v,_) -> v) up
  in    
  let e_init = process_sw m.mmemory (fun x -> x) sw_init in
  let e_step = process_sw m.mmemory (Corelang.add_pre_expr vl) sw_step in
  let e_init_out = process_sw copy_nd.node_outputs (fun x -> x) init_out in
  let e_update_out = process_sw  copy_nd.node_outputs (Corelang.add_pre_expr vl) update_out in
  let loc = Location.dummy_loc in
  let new_nd =
    { copy_nd with
    node_id = copy_nd.node_id ^ "_seal";
    node_locals = m.mmemory;
    node_stmts = [Eq
                    { eq_loc = loc;
                      eq_lhs = vl; 
                      eq_rhs = Corelang.mkexpr loc (Expr_arrow(e_init, e_step))
                    };
                 Eq
                    { eq_loc = loc;
                      eq_lhs = List.map (fun v -> v.var_id) copy_nd.node_outputs; 
                      eq_rhs = Corelang.mkexpr loc (Expr_arrow(e_init_out, e_update_out))
                    };
                 ];
    }
  in
  new_nd, orig_nd

  
let to_lustre basename prog m sw_init sw_step init_out update_out =
  let loc = Location.dummy_loc in
  let new_node, orig_nd = sw_to_lustre m sw_init sw_step init_out update_out in
  Global.type_env := Typing.type_node !Global.type_env new_node loc;
  Global.clock_env := Clock_calculus.clock_node !Global.clock_env loc new_node;

  (* Format.eprintf "%a@." Printers.pp_node new_node; *)

  (* Main output *)
  let output_file = !Options.dest_dir ^ "/" ^ basename ^ "_seal.lus" in
  let new_top =
    Corelang.mktop_decl Location.dummy_loc output_file false (Node new_node)
  in
  let out = open_out output_file in
  let fmt = Format.formatter_of_out_channel out in
  Format.fprintf fmt "%a@." Printers.pp_prog  [new_top];

  (* Verif output *)
  let output_file_verif = !Options.dest_dir ^ "/" ^ basename ^ "_seal_verif.lus" in
  let out_verif = open_out output_file_verif in
  let fmt_verif = Format.formatter_of_out_channel out_verif in
  let check_nd = Lustre_utils.check_eq new_node orig_nd in
  let check_top =
    Corelang.mktop_decl Location.dummy_loc output_file_verif false (Node check_nd)
  in
  Format.fprintf fmt_verif "%a@." Printers.pp_prog  (prog@[new_top;check_top]);
