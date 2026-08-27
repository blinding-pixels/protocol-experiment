require import AllCore List FSet.
require import ProtocolTypes CanonicalEncoding ProtocolPrimitives AuthorizationState.
require import WitnessFixtures AuthorizationWitnessTrace AuthorizationWitnessTraceTail.

(* Termination is independent of the concrete honest fixture: every loop
   iteration removes one signed fact before any validation branch is taken. *)
lemma normalize_test_signature_lossless :
  islossless NormalizeAuthorization(TestSignature).normalize.
proof.
  proc.
  while (true) (size remaining).
  - move=> z.
    inline TestSignature.verify.
    auto => />.
    rewrite size_behead.
    smt(size_ge0).
  - auto.
qed.
