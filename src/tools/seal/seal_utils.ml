open Lustre_types
open Utils
   
let report = Log.report ~plugin:"seal"
let seal_debug = ref false

type 'boolexpr guard = 'boolexpr list           
type ('guard, 'elem)  guarded_expr = 'guard * 'elem

                        
type element = IsInit | Expr of expr
type elem_boolexpr = element * bool

type elem_guarded_expr = (elem_boolexpr guard, element) guarded_expr
type 'ge mdef_t = 'ge list 
                                   
               (*          
type mdef_t = guarded_expr list
                *)
                     
let pp_elem fmt e =
  match e with
  | IsInit -> Format.fprintf fmt "init"
  | Expr e -> Format.fprintf fmt "%a" Printers.pp_expr e 

let pp_guard_list pp_elem fmt gl =
  (fprintf_list ~sep:";@ "
     (fun fmt (e,b) -> if b then pp_elem fmt e else Format.fprintf fmt "not(%a)" pp_elem e)) fmt gl
  
let pp_guard_expr pp_elem  fmt (gl,e) =
  Format.fprintf fmt "@[%a@] -> @[<hov 2>%a@]"
    (pp_guard_list pp_elem) gl
    pp_elem e

let pp_mdefs pp_elem fmt gel = fprintf_list ~sep:"@ " (pp_guard_expr pp_elem) fmt gel

                             
  
let deelem e =  match e with
    Expr e -> e
  | IsInit -> assert false (* Wasn't expecting isinit here: we are building values! *)

let is_eq_elem elem elem' =
  match elem, elem' with
  | IsInit, IsInit -> true
  | Expr e, Expr e' -> Corelang.is_eq_expr e e' 
  | _ -> false

let select_elem elem (gelem, _) =
  is_eq_elem elem gelem

let pp_gl pp_expr =
  fprintf_list ~sep:", " (fun fmt (e,b) -> Format.fprintf fmt "%s%a" (if b then "" else "NOT ") pp_expr e)
  
let pp_gl_short = pp_gl (fun fmt e -> Format.fprintf fmt "%i" e.Lustre_types.expr_tag) 
let pp_up fmt up = List.iter (fun (id,e) -> Format.fprintf fmt "%s->%i; " id e.expr_tag) up 

let pp_sys fmt sw = List.iter (fun (gl,up) ->
                        match gl with
                        | None ->
                           pp_up fmt up
                        | Some gl ->
                           Format.fprintf fmt "[@[%a@]] -> (%a)@ "
                             Printers.pp_expr gl pp_up up) sw
let pp_all_defs =
  (Utils.fprintf_list ~sep:",@ "
     (fun fmt (id, gel) -> Format.fprintf fmt "%s -> [@[<v 0>%a]@]"
                             id
                             (pp_mdefs pp_elem) gel))              
module UpMap =
      struct
        include Map.Make (
                    struct
                      type t = (ident * expr) list
                      let compare l1 l2 =
                        let proj l = List.map (fun (s,e) -> s, e.expr_tag) l in
                        compare (proj l1) (proj l2) 
                    end)
        let pp = pp_up 
      end
    
module Guards = struct
  include Set.Make (
              struct
                type t = (expr * bool) 
                let compare l1 l2 =
                  let proj (e,b) = e.expr_tag, b in
                  compare (proj l1) (proj l2) 
              end)
  let pp_short fmt s = pp_gl_short fmt (elements s)
  let pp_long fmt s = pp_gl Printers.pp_expr fmt (elements s)
end
                  
        
