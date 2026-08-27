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
  + proc.
    rcondf 10; first by
      auto;
      rewrite /minimal_noncanonical_operation /decode_operation.
    rcondt 11; first by
      auto;
      rewrite /minimal_noncanonical_operation /canonical_reencoding
        /defense_enabled /validation_success.
    rcondf 12; first by
      auto;
      rewrite /validation_error.
    auto; rewrite /validation_error; auto.
qed.

(* The positive production control uses the same stateful environment, exact
   authorization normalizer, and production validator as the mutation games.
   All three concrete seven-fact normalization passes are executed below; no
   authorization-success premise is imported. *)
lemma honest_edit_acceptance_probability_one &m :
  Pr[HonestEditAcceptanceWitness.main() @ &m :
       res = (true, 1)] = 1%r.
proof.
  byphoare => //.
  proc.
  inline *.

  rcondt ^while; first by auto.
  rcondt ^while; first by
    auto;
    rewrite /witness_fact_1 /witness_context_0 /witness_alice
      /witness_member_tag_alice /witness_fact_id_1
      /fact_signature_message /authorization_snapshot_lookup
      /apply_authorization_fact /authorization_fact_shape_valid
      /authorization_fact_shape_valid_kind /authorization_issuer_allowed
      /genesis_authorization_fact /apply_authorization_fact_kind
      /member_tag_known /empty_authorization_state;
    cbv delta;
    rewrite !inE; smt(in_fset0).
  rcondt ^while; first by auto.
  rcondt ^while; first by auto.
  rcondt ^while; first by auto.
  rcondt ^while; first by auto.
  rcondt ^while; first by auto.
  rcondf ^while; first by auto.

  rcondt ^while; first by auto.
  rcondt ^while; first by auto.
  rcondt ^while; first by auto.
  rcondt ^while; first by auto.
  rcondt ^while; first by auto.
  rcondt ^while; first by auto.
  rcondt ^while; first by auto.
  rcondf ^while; first by auto.

  rcondt ^while; first by auto.
  rcondt ^while; first by auto.
  rcondt ^while; first by auto.
  rcondt ^while; first by auto.
  rcondt ^while; first by auto.
  rcondt ^while; first by auto.
  rcondt ^while; first by auto.
  rcondf ^while; first by auto.

  auto.
qed.
