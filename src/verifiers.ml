open LustreSpec

open VerifierList

let active = ref None
           
let options () = 
  List.flatten (
    List.map Options_management.verifier_opt (
      List.map (fun m ->
	let module M = (val m : VerifierType.S) in
	(M.name, M.activate, M.options)
      ) verifiers
    ))
  
let verifier_list verifiers =
  List.fold_left (fun acc m ->
      let module M =  (val m : VerifierType.S) in
      (if acc = "" then "" else acc ^ ", ") ^ M.name
    ) "" verifiers
  
let get_active () =
  match !active with
  | None ->
     begin
       (* check that a single one is active and register it *)
       let found =
         List.fold_left (fun found m ->
             let module M =  (val m : VerifierType.S) in
             if M.is_active () then
               m::found
             else
               found
           ) [] verifiers
       in
       match found with
       | [] -> raise (Sys_error ("Please select one verifier in " ^ verifier_list verifiers))
       | [m] -> active := Some m; m
       | _ -> raise (Sys_error ("Too many selected verifiers: " ^ verifier_list found))
     end

  | Some m -> m


                
                (* Local Variables: *)
                (* compile-command:"make -C .." *)
                (* End: *)
