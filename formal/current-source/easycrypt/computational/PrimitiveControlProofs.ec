require import AllCore List.
require import ProtocolTypes CanonicalEncoding ProtocolPrimitives WitnessFixtures.
require PrimitiveGames.
clone import PrimitiveGames as PG.

(* Deliberately insecure primitive control.  The adversary makes no signing
   query, constructs a TestSignature value directly, and asks the actual logged
   verification oracle to verify it.  This demonstrates that the named
   multi-user EUF-CMA game and its query logs are reachable and nonconstant. *)
op control_verification_key : verification_key = VerificationKey 77.
op control_message : signature_message =
  AuthorizationFactSignatureMessage witness_fact_1.
op control_signature : signature =
  {| sig_verification_key = control_verification_key;
     sig_bytes = SignatureBytes control_message |}.
op control_forgery : PG.signature_forgery =
  {| sf_verification_key = control_verification_key;
     sf_message = control_message;
     sf_signature = control_signature |}.

module TestSignatureMultiUserForgery(O : PG.LOGGED_SIGNATURE_ORACLE) = {
  proc forge(initial_state : protocol_state) : PG.signature_forgery option = {
    var valid : bool;
    valid <@ O.verify(
      control_verification_key,
      control_message,
      control_signature.`sig_bytes
    );
    return Some control_forgery;
  }
}.

lemma test_signature_multi_user_eufcma_probability_one
    &m (initial : protocol_state) :
  Pr[
    PG.MultiUserEUFCMAGame(
      TestSignatureMultiUserForgery,
      TestSignature
    ).main(initial) @ &m : res
  ] = 1%r.
proof.
  byphoare => //.
  proc.
  inline *.
  auto.
  rewrite /PG.signature_forgery_valid /control_forgery
    /control_signature /control_verification_key /control_message /=.
  by [].
qed.
