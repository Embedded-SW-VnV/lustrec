let active = ref false

module Verifier =
  (struct
    include VerifierType.Default
    let name = "seal"
    let options = []
    let activate () = active := true
    let is_active () = !active
    let run basename prog machines = ()
                    
  end: VerifierType.S)
    
