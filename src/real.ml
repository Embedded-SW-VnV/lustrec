(* (a, b, c) means a * 10^-b. c is the original string *)
type t = Num.num * int * string 

let pp fmt (c, e, s) =
    Format.fprintf fmt "%s%s"
      s
      (if String.get s (-1 + String.length s) = '.' then "0" else "")

let pp_ada fmt (c, e, s) =
  Format.fprintf fmt "%s.0*1.0e-%i" (Num.string_of_num c) e
  
let create m e s = Num.num_of_string m, e, s
let create_num n s = n, 0, s
                   
let to_num (c, e, s) =
  let num_10 = Num.num_of_int 10 in
  Num.(c // (num_10 **/ (num_of_int e)))

let to_string (_, _, s) = s
                        
let eq r1 r2 =
  Num.eq_num (to_num r1) (to_num r2)
  
  
let num_binop op r1 r2 =
  let n1 = to_num r1 and n2 = to_num r2 in
  op n1 n2
  
let arith_binop op r1 r2 =
  let r = num_binop op r1 r2 in
  create_num r (Num.string_of_num r)
  
let add   = arith_binop (Num.(+/))
let minus = arith_binop (Num.(-/))
let times = arith_binop (Num.( */))
let div   = arith_binop (Num.(//)) 

let uminus (c, e, s) = Num.minus_num c, e, "-" ^ s

let lt = num_binop (Num.(</))
let le = num_binop (Num.(<=/))
let gt = num_binop (Num.(>/))
let ge = num_binop (Num.(>=/))
let diseq = num_binop (Num.(<>/))
let eq = num_binop (Num.(=/))

let zero = Num.num_of_int 0, 0, "0.0"

let is_zero r = Num.eq_num (to_num r) (Num.num_of_int 0)
let is_one r = Num.eq_num (to_num r) (Num.num_of_int 1)
