
let get_type () (*fixformat*) =
  let _total,_int = !Options.ap_fixed_format in
  "ap_fixed<" ^ string_of_int _total ^ "," ^ string_of_int _int ^ ">" 
