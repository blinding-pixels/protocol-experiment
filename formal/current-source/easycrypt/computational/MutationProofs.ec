require import AllCore List FSet.
require import ProtocolTypes CanonicalEncoding ProtocolPrimitives AuthorizationState.
require import ProtocolChecks ProtocolOracles UnauthorizedGame WitnessFixtures MutationWitnesses.

(* A minimal noncanonical candidate reaches the production validator but is
   rejected before authorization normalization.  This proves the canonical
   check is an executable, non-vacuous branch of the same ValidateOperation
   procedure used by UnauthorizedReal. *)
module MinimalNonCanonicalRejection = {
  proc main() : bool = {
    var envelope : operation_envelope;
    var operation : signed_operation;
    var view : public_view;
    var state : protocol_state;
    var result : validation_result;

    envelope <- witness_edit_envelope
      (ProtocolDomain 1)
      (1)
      (witness_document)
      (OperationId 900)
      (witness_bob_old)
      (CapEdit)
      (fset1 witness_base_node)
      (AuthorizationDigest 0)
      (EditBody EditText (Payload 900))
      (Nonce 900);
    operation <-
      {| so_raw = NonCanonicalWire envelope (RawBytes 900);
         so_signature =
           {| sig_verification_key =
                witness_bob_old.`p_verification_key;
              sig_bytes =
                SignatureBytes
                  (AuthorizationFactSignatureMessage witness_fact_1) |} |};
    view <- {| pv_facts = []; pv_observed_fact_ids = fset0 |};
    state <- witness_protocol_state witness_base_node fset0;

    result <@ ValidateOperation(TestSignature).validate(
      Production,
      operation,
      view,
      state
    );
    return
      ! result.`vr_accepted /\
      result.`vr_failure = Some FailureCanonicalReencoding;
  }
}.

lemma noncanonical_rejection_probability_one &m :
  Pr[MinimalNonCanonicalRejection.main() @ &m : res] = 1%r.
proof.
  byphoare=> //.
  proc.
  inline *.
  auto.
qed.
