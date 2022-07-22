(* (a, b, c) means a * 10^-b. c is the original string *)
type t = Q.t * int * string 

let pp fmt (c, e, s) =
    Format.fprintf fmt "%s%s"
      s
      (if String.get s (-1 + String.length s) = '.' then "0" else "")

let pp_ada fmt (c, e, s) =
  Format.fprintf fmt "%s.0*1.0e-%i" (Q.to_string c) e
  
let create m e s = Q.of_string m, e, s

let create_q q s = q, 0, s
                   
(*
let to_num (c, e, s) =
  let num_10 = Num.num_of_int 10 in
  Num.(c // (num_10 **/ (num_of_int e)))
 *)
                 
let rec to_q (c, e, s) =
  if e = 0 then
    c
  else
    if e > 0 then Q.div (to_q (c,e-1,s)) (Q.of_int 10)
    else (* if exp<0 then *)
      Q.mul
        (to_q (c,e+1,s))
        (Q.of_int 10)

let to_num = to_q
           
let to_string (_, _, s) = s
                        
let eq r1 r2 =
  Q.equal (to_q r1) (to_q r2)
  
  
let num_binop op r1 r2 =
  let n1 = to_num r1 and n2 = to_num r2 in
  op n1 n2
  
let arith_binop op r1 r2 =
  let r = num_binop op r1 r2 in
  create_q r (Q.to_string r)
  
let add   = arith_binop Q.add
let minus = arith_binop Q.sub
let times = arith_binop Q.mul
let div   = arith_binop Q.div 

let uminus (c, e, s) = Q.neg c, e, "-" ^ s

let lt = num_binop (Q.(<))
let le = num_binop (Q.(<=))
let gt = num_binop (Q.(>))
let ge = num_binop (Q.(>=))
let diseq = num_binop (Q.(<>))
let eq = num_binop (Q.(=))

let zero = Q.zero, 0, "0.0"

let is_zero r = Q.equal (to_num r) Q.zero
let is_one r = Q.equal (to_num r) Q.one
