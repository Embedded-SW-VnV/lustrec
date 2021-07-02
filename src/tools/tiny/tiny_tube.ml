(* 
TODO:

- export du tube sur la tete de boucle:
  - par exemple un tube par dimension en 2d: temps x valeur
  - en sage ? en gnuplot? en tikz?
  - deux facon de visualiser le partitionnement
    - si on choisi un tube 2d, par exemple la variable x, on doit pouvoir visualiser le split du tube en fonction d'une variable booleenne. Par exemple on choisi b1 et on voit deux couleurs sur le tube de x. Ou on se restreint a b1 true ou b1 false 
    - on doit aussi pouvoir afficher globalement pour une variable booleen le split. On choisi par exemple b1 de facon gloable et tous les tubes sont raffines en b1 true / b1 false / b1 both / b1 split enfin pour avoir deux plots separes.

   - par exemple un csv
   nb_temps, x_min, x_max, y_min, y_max, b1_true_x_min, b1_true_x_max, b1_true_y_min, b1_true_y_max, ....


  - 
- export de l'ast en latex avec des instructions tikz puis ensuite l'affichage des elements abstraits a chaque point de programme pour les articles. On peut desactiver ou activer les domaines grace aux options

*)


let pp_var fmt ((n,t),ctx) =
  (* Tiny.Ast.Var.pp_ fmt v *)
  match ctx with
  | None ->
    Format.fprintf fmt "%s" n  
  | Some ((bv, _),b) ->
     Format.fprintf fmt "%s __ %s = %b" n bv b  

  
let pp_bound fmt b = Tiny.Scalar.pp fmt b 

module type S =
  sig
    module Results: Tiny.Analyze.Results
    val list: (int * Results.Dom.t) list
    val bounds:  ((Tiny.Ast.Var.t * (Tiny.Ast.Var.t * bool) option) * (Tiny.Scalar.t * Tiny.Scalar.t)) list
  end
  
let process env ast results =
  let module Results = (val results: Tiny.Analyze.Results) in
  let module Dom = Results.Dom in
  let module PrintResults = Tiny.PrintResults.Make (Dom) in
  let m = Results.results in
  
  let while_loc = Tiny.Ast.get_main_while_loc ast in
  let list = PrintResults.get_unrolled_info m while_loc in
  let join =
    match list with
    | [] -> Dom.bottom env
    | (_,hd)::tl -> List.fold_left (fun accu (_,e) -> Dom.join accu e) hd tl
  in
  let bounds = Dom.to_bounds join in
  let module M = struct
      module Results = Results
      module PrintResults = PrintResults
      let list = list
      let bounds = bounds
    end
  in
  (module M: S)
  (*                 
let build f_header f_content env ast results =
  let module Results = (val results: Tiny.Analyze.Results) in
  let module Dom = Results.Dom in
  let module PrintResults = Tiny.PrintResults.Make (Dom) in
  let m = Results.results in
  
  let while_loc = Tiny.Ast.get_main_while_loc ast in
  let list = PrintResults.get_unrolled_info m while_loc in
  let join =
    match list with
    | [] -> Dom.bottom env
    | (_,hd)::tl -> List.fold_left (fun accu (_,e) -> Dom.join accu e) hd tl
  in
  let bounds = Dom.to_bounds join in
  f_header bounds;
  f_content list
  *)

let pp_bounds fmt bounds =
  List.iter (fun ((v,ctx) as x, (min, max)) ->
      
      Format.fprintf fmt
        "%a in %a,%a@."
        pp_var x
        pp_bound min
        pp_bound max)
    bounds
  
let pp env ast results fmt =
  let m = process env ast results in
  let module M = (val m: S) in
  pp_bounds fmt  M.bounds;
  Format.fprintf fmt "Tube: %i@." (List.length M.list);
  List.iter (fun (idx, elem) ->
      Format.fprintf fmt "%i -> %a@." idx M.Results.Dom.fprint elem) M.list

let export env ast results fmt =
  let m = process env ast results in
  let module M = (val m: S) in
  List.iter (fun (x, (min, max)) ->
      Format.fprintf fmt
        "%a in %a,%a@."
        pp_var x
        pp_bound min
        pp_bound max)
    M.bounds;
  Format.fprintf fmt "Tube: %i@." (List.length M.list);
  List.iter (fun (idx, elem) ->
      Format.fprintf fmt
        "%i -> %a@."
        idx
        pp_bounds (M.Results.Dom.to_bounds elem)
    ) M.list

let export_to_wide_csv  env ast results fmt =
  let m = process env ast results in
  let module M = (val m: S) in
  let bounds = List.map (fun (idx, elem) -> idx, M.Results.Dom.to_bounds elem) M.list in
  (* Gather all variable ids *)
  let module VarIdSet = Set.Make (
                         struct
                           type t = Tiny.Ast.Var.t * (Tiny.Ast.Var.t * bool) option
                           let compare = compare
                         end)
  in
  let var_ids = List.fold_left (
                    fun accu (_, bounds) ->
                    List.fold_left (fun accu (vctx, _) -> VarIdSet.add vctx accu) accu bounds
                  ) VarIdSet.empty bounds
  in
  let ordered_list = VarIdSet.elements var_ids in
  Format.fprintf fmt "timestep,%a@."
    (Utils.fprintf_list ~sep:","
       (fun fmt ((n,_),ctx) ->
         let pp fmt =
           match ctx with
             None ->
              Format.fprintf fmt "%s" n
           | Some ((bn,_),b) ->
              Format.fprintf fmt "%s_//%s_eq_%b" n bn b
         in
         Format.fprintf fmt "%t_min,%t_max" pp pp
    ))
    ordered_list;
  Format.fprintf fmt "%a@."
    (Utils.fprintf_list ~sep:"@."
    (fun fmt (idx, bounds_idx) ->
      Format.fprintf fmt "@[<h 0>%i, %a@]"
        idx
        (Utils.fprintf_list ~sep:", "
           (fun fmt (min_, max_) ->
             let pp_bound fmt b = match b with
               | None -> Format.fprintf fmt ","
               | Some b -> Tiny.Scalar.pp fmt b
             in
             Format.fprintf fmt "%a, %a" pp_bound min_ pp_bound max_))
        (List.map (fun v -> if List.mem_assoc v bounds_idx then
                              let min_, max_ = List.assoc v bounds_idx in
                              Some min_, Some max_
                            else
                              None, None
           ) ordered_list)
    ))
    bounds;
  ()


let export_to_csv  env ast results fmt =
  let m = process env ast results in
  let module M = (val m: S) in
  let bounds = List.map (fun (idx, elem) ->
                   idx,
                   try M.Results.Dom.to_bounds elem with Tiny.Relational.BotEnv -> Format.eprintf "Issues exporting env %a to bounds: bottom!@." M.Results.Dom.fprint elem; assert false
                 ) M.list
  in
  (* Gather all variable ids *)
  let pp_vctx fmt ((n,t), ctx ) =
    match ctx with
    | None -> Format.fprintf fmt "%s,%a,," n (Tiny.Ast.pp_base_type) t
    | Some ((bname,_ (* type should be bool *) ), bval) ->
        Format.fprintf fmt "%s,%a,%s,%b" n (Tiny.Ast.pp_base_type) t bname bval
  in
  let pp_bound fmt (min_, max_) =
    Format.fprintf fmt "%a,%a" Tiny.Scalar.pp min_ Tiny.Scalar.pp max_
  in
  Format.fprintf fmt "timestep,varid,type,boolpart,boolval,min,max@.";
  Utils.fprintf_list ~sep:"@." (
      fun fmt (idx, idx_bounds) ->
      Utils.fprintf_list ~sep:"@." (fun fmt (vctx, vctx_bound) ->
          Format.fprintf fmt "%i,%a,%a" idx pp_vctx vctx pp_bound vctx_bound
        ) fmt idx_bounds
    ) fmt bounds

  
