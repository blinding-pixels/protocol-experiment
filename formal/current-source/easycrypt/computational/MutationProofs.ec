require import AllCore List FSet.
require import ProtocolTypes CanonicalEncoding ProtocolPrimitives AuthorizationState.
require import ProtocolChecks ProtocolOracles UnauthorizedGame WitnessFixtures MutationWitnesses.

(* A minimal noncanonical candidate reaches the production validator but is
   rejected before authorization normalization.  This proves the canonical
   check is an executable, non-vacuous branch of the same ValidateOperation
   procedure used by UnauthorizedReal. *)
op minimal_noncanonical_envelope : operation_envelope =
  witness_edit_envelope
    (ProtocolDomain 1)
    (1)
    (witness_document)
    (OperationId 900)
    (witness_bob_old)
    (CapEdit)
    (fset1 witness_base_node)
    (AuthorizationDigest 0)
    (EditBody EditText (Payload 900))
    (Nonce 900).

op minimal_noncanonical_operation : signed_operation =
  {| so_raw =
       NonCanonicalWire minimal_noncanonical_envelope (RawBytes 900);
     so_signature =
       {| sig_verification_key = witness_bob_old.`p_verification_key;
          sig_bytes =
            SignatureBytes
              (AuthorizationFactSignatureMessage witness_fact_1) |} |}.

op minimal_noncanonical_view : public_view =
  {| pv_facts = []; pv_observed_fact_ids = fset0 |}.

op minimal_noncanonical_state : protocol_state =
  witness_protocol_state witness_base_node fset0.

lemma noncanonical_rejection_probability_one &m :
  Pr[ValidateOperation(TestSignature).validate(
       Production,
       minimal_noncanonical_operation,
       minimal_noncanonical_view,
       minimal_noncanonical_state
     ) @ &m :
       ! res.`vr_accepted /\
       res.`vr_failure = Some FailureCanonicalReencoding] = 1%r.
proof.
  byphoare
    (: mode = Production /\
       signed_operation = minimal_noncanonical_operation /\
       view = minimal_noncanonical_view /\
       state = minimal_noncanonical_state
       ==>
       ! res.`vr_accepted /\
       res.`vr_failure = Some FailureCanonicalReencoding)
    => //.
  proc.
  rcondf 10; first by
    auto;
    rewrite /minimal_noncanonical_operation /decode_operation.
  rcondt 10; first by
    auto;
    rewrite /minimal_noncanonical_operation /canonical_reencoding
      /defense_enabled /validation_success.
  auto.
qed.
