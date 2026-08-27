require import AllCore List FSet.
require import ProtocolTypes CanonicalEncoding ProtocolPrimitives AuthorizationState.
require import ProtocolChecks ProtocolOracles UnauthorizedGame WitnessFixtures MutationWitnesses.
require import AuthorizationWitnessTrace HonestFixtureContract.

(* Exact deterministic objects used by [HonestEditAcceptanceWitness.main].
   Keeping them named prevents later validator proofs from rebuilding the
   seven-fact authorization calculation or the operation-signing transcript. *)

op witness_base_state_exact : protocol_state =
  witness_protocol_state witness_base_node witness_context_7.

op witness_base_view_exact : public_view =
  witness_public_view witness_base_signed_facts witness_context_7.

op witness_honest_edit_envelope : operation_envelope =
  witness_edit_envelope
    (ProtocolDomain 1)
    1
    witness_document
    (OperationId 100)
    witness_bob_old
    CapEdit
    (fset1 witness_base_node)
    (authorization_digest_of witness_authorization_state_7)
    witness_edit_body_one
    (Nonce 100).

op witness_honest_edit_operation : signed_operation =
  {| so_raw = encode_operation witness_honest_edit_envelope;
     so_signature =
       {| sig_verification_key = witness_bob_old.`p_verification_key;
          sig_bytes =
            SignatureBytes
              (operation_signature_message
                Production witness_honest_edit_envelope) |} |}.

lemma witness_sign_honest_edit_operation :
  hoare [WitnessFixtures.sign_operation :
       mode = Production
    /\ envelope = witness_honest_edit_envelope
    /\ signing_key = witness_bob_old.`p_verification_key
    ==>
    res = witness_honest_edit_operation].
proof.
  by proc; inline TestSignature.sign; auto.
qed.

lemma witness_honest_edit_decodes :
  decode_operation witness_honest_edit_operation.`so_raw =
    Some witness_honest_edit_envelope.
proof.
  by rewrite /witness_honest_edit_operation.
qed.

lemma witness_honest_edit_is_canonical :
  canonical_reencoding witness_honest_edit_operation.`so_raw.
proof.
  by rewrite /witness_honest_edit_operation.
qed.

lemma witness_honest_predecessor_set :
  witness_honest_edit_envelope.`oe_direct_predecessors =
    fset1 witness_base_node.
proof.
  by rewrite /witness_honest_edit_envelope /witness_edit_envelope.
qed.

lemma witness_honest_predecessor_elems :
  elems witness_honest_edit_envelope.`oe_direct_predecessors =
    [witness_base_node].
proof.
  rewrite witness_honest_predecessor_set.
  exact (elems_fset1 witness_base_node).
qed.

lemma witness_honest_predecessors_exist :
  all_predecessors_exist
    witness_base_state_exact
    witness_honest_edit_envelope.`oe_direct_predecessors.
proof.
  rewrite /all_predecessors_exist
    witness_honest_predecessor_elems
    /witness_base_state_exact /witness_protocol_state /=.
  by rewrite in_fset1.
qed.

lemma witness_honest_exact_closure :
  exact_predecessor_closure
    witness_base_state_exact
    witness_honest_edit_envelope.`oe_direct_predecessors =
  Some witness_context_7.
proof.
  rewrite /exact_predecessor_closure
    witness_honest_predecessor_elems
    /witness_base_state_exact /witness_protocol_state
    /witness_closure_map /=.
  by rewrite fsetU0.
qed.

lemma witness_base_fact_ids :
  fact_ids_of_signed_facts witness_base_signed_facts = witness_context_7.
proof.
  rewrite /witness_base_signed_facts
    !fact_ids_of_signed_facts_cons fact_ids_of_signed_facts_nil
    /witness_signed_fact_1 /witness_signed_fact_2
    /witness_signed_fact_3 /witness_signed_fact_4
    /witness_signed_fact_5 /witness_signed_fact_6
    /witness_signed_fact_7 /witness_signed_fact_of
    /witness_fact_1 /witness_fact_2 /witness_fact_3
    /witness_fact_4 /witness_fact_5 /witness_fact_6
    /witness_fact_7
    /witness_context_7 /witness_context_6 /witness_context_5
    /witness_context_4 /witness_context_3 /witness_context_2
    /witness_context_1.
  apply/fsetP=> id.
  rewrite !inE.
  smt().
qed.

lemma witness_base_signed_facts_for_context :
  signed_facts_for_ids witness_base_signed_facts witness_context_7 =
    witness_base_signed_facts.
proof.
  rewrite /witness_base_signed_facts
    !signed_facts_for_ids_cons signed_facts_for_ids_nil
    /witness_signed_fact_1 /witness_signed_fact_2
    /witness_signed_fact_3 /witness_signed_fact_4
    /witness_signed_fact_5 /witness_signed_fact_6
    /witness_signed_fact_7 /witness_signed_fact_of
    /witness_fact_1 /witness_fact_2 /witness_fact_3
    /witness_fact_4 /witness_fact_5 /witness_fact_6
    /witness_fact_7
    /witness_context_7 /witness_context_6 /witness_context_5
    /witness_context_4 /witness_context_3 /witness_context_2
    /witness_context_1.
  by rewrite !inE; smt().
qed.

lemma witness_honest_domain_version :
     witness_honest_edit_envelope.`oe_protocol_domain =
       expected_protocol_domain
  /\ witness_honest_edit_envelope.`oe_protocol_version =
       expected_protocol_version.
proof.
  by rewrite /witness_honest_edit_envelope /witness_edit_envelope
    /expected_protocol_domain /expected_protocol_version.
qed.

lemma witness_honest_document_binding :
  witness_honest_edit_envelope.`oe_document_id =
    witness_base_state_exact.`ps_document_id.
proof.
  by rewrite /witness_honest_edit_envelope /witness_edit_envelope
    /witness_base_state_exact /witness_protocol_state.
qed.

lemma witness_honest_freshness :
     witness_honest_edit_envelope.`oe_operation_id
       \notin witness_base_state_exact.`ps_seen_operation_ids
  /\ witness_honest_edit_envelope.`oe_nonce
       \notin witness_base_state_exact.`ps_seen_nonces.
proof.
  by rewrite /witness_honest_edit_envelope /witness_edit_envelope
    /witness_base_state_exact /witness_protocol_state !inE.
qed.

lemma witness_bob_old_member_active_state_7 :
  member_active Production witness_authorization_state_7 witness_bob_old.
proof.
  rewrite /member_active /witness_authorization_state_7
    /witness_member_grant_alice_entry
    /witness_member_grant_bob_old_entry
    /principal_matches /defense_enabled.
  smt(in_fsetU in_fset1 in_fset0).
qed.

lemma witness_bob_old_edit_active_state_7 :
  capability_active
    Production witness_authorization_state_7 witness_bob_old CapEdit.
proof.
  rewrite /capability_active /witness_authorization_state_7
    /witness_capability_grant_bob_old_edit_entry
    /principal_matches /defense_enabled.
  smt(in_fsetU in_fset1 in_fset0).
qed.

lemma witness_honest_required_capability :
  required_capability_for_operation
    witness_honest_edit_envelope.`oe_operation_kind
    witness_honest_edit_envelope.`oe_operation_body = CapEdit.
proof.
  by rewrite /witness_honest_edit_envelope /witness_edit_envelope
    /witness_edit_body_one /required_capability_for_operation.
qed.

lemma witness_honest_operation_body_valid :
  operation_body_valid_for_envelope witness_honest_edit_envelope.
proof.
  by rewrite /witness_honest_edit_envelope /witness_edit_envelope
    /witness_edit_body_one /operation_body_valid_for_envelope
    /operation_body_kind /operation_body_valid.
qed.

lemma witness_honest_authorization_digest :
  witness_honest_edit_envelope.`oe_authorization_digest =
    authorization_digest_of witness_authorization_state_7.
proof.
  by rewrite /witness_honest_edit_envelope /witness_edit_envelope.
qed.

lemma witness_honest_author_key_binding :
  witness_honest_edit_operation.`so_signature.`sig_verification_key =
    witness_honest_edit_envelope.`oe_author.`p_verification_key.
proof.
  by rewrite /witness_honest_edit_operation
    /witness_honest_edit_envelope /witness_edit_envelope.
qed.
