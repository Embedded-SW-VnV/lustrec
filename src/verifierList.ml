let registered : (module VerifierType.S) list ref = ref []

let verifiers () = !registered
(* [
 *   (module Seal_verifier.Verifier : VerifierType.S);
 *   (module Zustre_verifier.Verifier : VerifierType.S);
 *   (module Tiny_verifier.Verifier : VerifierType.S);
 * ] *)
