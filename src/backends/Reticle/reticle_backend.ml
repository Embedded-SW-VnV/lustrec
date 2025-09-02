(* Reticle backend

   - based on EMF backend
   - TODO add extra normalisation
   - TODO adds export of the dependency graph for variables
*)

(*    Reticle_backend.translate fmt basename prog machine_code; *)
open Machine_code_types
let translate fmt basename prog machine_code =
  List.iter (fun m ->
      let annot = m.mannot in
      ()
    ) machine_code;
  EMF_backend.translate fmt basename prog machine_code
