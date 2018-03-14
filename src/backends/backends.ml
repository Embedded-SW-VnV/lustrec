(* Backend-specific options *)
let join_guards = ref true

let setup () =
  match !Options.output with
  | "emf" ->
     (* Not merging branches *)
     join_guards := false;
     (* In case of a default "int" type, substitute it with the legal int32 value *)
     if !Options.int_type = "int" then
       Options.int_type := "int32"
  | _ -> ()

let is_functional () = 
  match !Options.output with
  | "horn" | "lustre" | "acsl" | "emf" -> true
  | _ -> false

                             
(* Special treatment of arrows in lustre backend. We want to keep them *)
let unfold_arrow () =
  match !Options.output with
  | "lustre" -> false
  | _ -> true

(* Forcing ite normalization *)
let alias_ite () =
  match !Options.output with
  | "emf" -> true
  | _ -> false

(* Forcing basic functions normalization *)
let alias_internal_fun () =
  match !Options.output with
  | "emf" -> true
  | _ -> false

let get_normalization_params () = {
    Normalization.unfold_arrow_active = unfold_arrow ();
    force_alias_ite = alias_ite ();
    force_alias_internal_fun = alias_internal_fun ();
  }


(* Local Variables: *)
(* compile-command: "make -k -C .." *)
(* End: *)
