let registered : (module VerifierType.S) list ref = ref []

let verifiers () = !registered
  (* [
   *   @LUSTREV_SEAL@
   *   @LUSTREV_ZUSTRE@
   *   @LUSTREV_TINY@
   * ] *)
