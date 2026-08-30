require import AllCore List FSet.
require import ProtocolTypes CanonicalEncoding ProtocolPrimitives AuthorizationState.
require import ProtocolChecks ProtocolOracles WitnessFixtures MutationWitnesses.
require import AuthorizationWitnessTrace HonestOperationContract.
require import ValidatorCharacterization MutationGameProofs.

op mutation_signed_operation
    (signed_mode : validator_mode)
    (envelope : operation_envelope)
    (signing_key : verification_key) : signed_operation =
  {| so_raw = encode_operation envelope;
     so_signature =
       {| sig_verification_key = signing_key;
          sig_bytes =
            SignatureBytes (operation_signature_message signed_mode envelope) |} |}.

lemma base_singleton_predecessors_exist :
  all_predecessors_exist witness_base_state_exact (fset1 witness_base_node).
proof.
  have := witness_honest_predecessors_exist.
  by rewrite /witness_honest_edit_envelope /witness_edit_envelope.
qed.

lemma base_singleton_exact_closure :
  exact_predecessor_closure witness_base_state_exact (fset1 witness_base_node) =
    Some witness_context_7.
proof.
  have := witness_honest_exact_closure.
  by rewrite /witness_honest_edit_envelope /witness_edit_envelope.
qed.

lemma base_document_is_witness_document :
  witness_base_state_exact.`ps_document_id = witness_document.
proof.
  by rewrite /witness_base_state_exact /witness_protocol_state.
qed.

lemma base_any_fresh (oid : operation_id) (n : nonce) :
     oid \notin witness_base_state_exact.`ps_seen_operation_ids
  /\ n \notin witness_base_state_exact.`ps_seen_nonces.
proof.
  by rewrite /witness_base_state_exact /witness_protocol_state !inE.
qed.

lemma edit_body_one_required_capability :
  required_capability_for_operation OpEdit witness_edit_body_one = CapEdit.
proof.
  have := witness_honest_required_capability.
  by rewrite /witness_honest_edit_envelope /witness_edit_envelope.
qed.

lemma edit_body_one_valid :
  operation_body_valid_for_envelope
    (witness_edit_envelope
      (ProtocolDomain 1) 1 witness_document (OperationId 1)
      witness_bob_old CapEdit (fset1 witness_base_node)
      (authorization_digest_of witness_authorization_state_7)
      witness_edit_body_one (Nonce 1)).
proof.
  by rewrite /witness_edit_envelope /witness_edit_body_one
    /operation_body_valid_for_envelope /operation_body_kind
    /operation_body_valid.
qed.

lemma bob_new_member_inactive_production :
  ! member_active Production witness_authorization_state_7 witness_bob_new.
proof.
  rewrite /member_active /witness_authorization_state_7
    /witness_member_grant_alice_entry /witness_member_grant_bob_old_entry
    /principal_matches /defense_enabled /witness_alice
    /witness_bob_old /witness_bob_new.
  smt(in_fsetU in_fset1 in_fset0).
qed.

lemma bob_new_edit_inactive_production :
  ! capability_active
      Production witness_authorization_state_7 witness_bob_new CapEdit.
proof.
  rewrite /capability_active /witness_authorization_state_7
    /witness_capability_grant_alice_admin_entry
    /witness_capability_grant_alice_history_entry
    /witness_capability_grant_alice_puncture_entry
    /witness_capability_grant_alice_beekem_entry
    /witness_capability_grant_bob_old_edit_entry
    /principal_matches /defense_enabled /witness_alice
    /witness_bob_old /witness_bob_new.
  smt(in_fsetU in_fset1 in_fset0).
qed.

lemma bob_new_member_active_without_incarnation :
  member_active
    (WithoutDefense DefenseIncarnationBinding)
    witness_authorization_state_7 witness_bob_new.
proof.
  rewrite /member_active /witness_authorization_state_7
    /witness_member_grant_alice_entry /witness_member_grant_bob_old_entry
    /principal_matches /defense_enabled /witness_alice
    /witness_bob_old /witness_bob_new.
  smt(in_fsetU in_fset1 in_fset0).
qed.

lemma bob_new_edit_active_without_incarnation :
  capability_active
    (WithoutDefense DefenseIncarnationBinding)
    witness_authorization_state_7 witness_bob_new CapEdit.
proof.
  rewrite /capability_active /witness_authorization_state_7
    /witness_capability_grant_alice_admin_entry
    /witness_capability_grant_alice_history_entry
    /witness_capability_grant_alice_puncture_entry
    /witness_capability_grant_alice_beekem_entry
    /witness_capability_grant_bob_old_edit_entry
    /principal_matches /defense_enabled /witness_alice
    /witness_bob_old /witness_bob_new.
  smt(in_fsetU in_fset1 in_fset0).
qed.

op mutation_author_key_envelope : operation_envelope =
  witness_edit_envelope
    (ProtocolDomain 1) 1 witness_document (OperationId 202)
    witness_bob_old CapEdit (fset1 witness_base_node)
    (authorization_digest_of witness_authorization_state_7)
    witness_edit_body_one (Nonce 202).

op mutation_author_key_operation : signed_operation =
  mutation_signed_operation
    Production mutation_author_key_envelope witness_alice.`p_verification_key.

lemma mutation_author_key_decodes :
  decode_operation mutation_author_key_operation.`so_raw =
    Some mutation_author_key_envelope.
proof. by rewrite /mutation_author_key_operation /mutation_signed_operation. qed.

lemma mutation_author_key_canonical :
  canonical_reencoding mutation_author_key_operation.`so_raw.
proof. by rewrite /mutation_author_key_operation /mutation_signed_operation. qed.

lemma mutation_author_key_production_rejects :
  ! base_facts_edit_decoded_accepts Production mutation_author_key_operation
      mutation_author_key_envelope witness_base_view_exact
      witness_base_state_exact.
proof.
  rewrite /base_facts_edit_decoded_accepts /base_facts_common_accepts
    /mutation_author_key_operation /mutation_signed_operation
    /mutation_author_key_envelope /witness_edit_envelope
    /witness_alice /witness_bob_old /defense_enabled.
  smt().
qed.

lemma mutation_author_key_removed_accepts :
  base_facts_edit_decoded_accepts
    (WithoutDefense DefenseAuthorKeyBinding)
    mutation_author_key_operation mutation_author_key_envelope
    witness_base_view_exact witness_base_state_exact.
proof.
  rewrite /base_facts_edit_decoded_accepts /base_facts_common_accepts
    /mutation_author_key_operation /mutation_signed_operation
    /mutation_author_key_envelope /witness_edit_envelope /defense_enabled.
  rewrite base_singleton_predecessors_exist base_singleton_exact_closure
    witness_base_view_facts witness_base_fact_ids
    witness_base_view_observed_fact_ids base_document_is_witness_document
    witness_bob_old_member_active_state_7
    witness_bob_old_edit_active_state_7 edit_body_one_required_capability.
  have Hfresh := base_any_fresh (OperationId 202) (Nonce 202).
  rewrite /operation_signature_message /operation_transcript /defense_enabled.
  smt(edit_body_one_valid).
qed.

lemma mutation_author_key_wins_probability_one &m :
  Pr[CheckedMutationRunner.run(
       DefenseAuthorKeyBinding, mutation_author_key_operation,
       witness_base_view_exact, witness_base_state_exact) @ &m :
     res = (true, 1)] = 1%r.
proof.
  byphoare
    (: removed = DefenseAuthorKeyBinding
       /\ operation = mutation_author_key_operation
       /\ view = witness_base_view_exact
       /\ state = witness_base_state_exact
       ==> res = (true, 1)) => //.
  + conseq (base_facts_edit_mutation_run_wins
      DefenseAuthorKeyBinding mutation_author_key_operation
      mutation_author_key_envelope witness_base_view_exact
      witness_base_state_exact) => //.
    + exact witness_base_view_facts.
    + exact witness_base_state_creator.
    + exact mutation_author_key_decodes.
    + by rewrite /mutation_author_key_envelope /witness_edit_envelope.
    + exact mutation_author_key_canonical.
    + exact mutation_author_key_production_rejects.
    + exact mutation_author_key_removed_accepts.
  + conseq checked_mutation_runner_lossless => //.
qed.

op mutation_incarnation_envelope : operation_envelope =
  witness_edit_envelope
    (ProtocolDomain 1) 1 witness_document (OperationId 203)
    witness_bob_new CapEdit (fset1 witness_base_node)
    (authorization_digest_of witness_authorization_state_7)
    witness_edit_body_one (Nonce 203).

op mutation_incarnation_operation : signed_operation =
  mutation_signed_operation Production mutation_incarnation_envelope
    witness_bob_new.`p_verification_key.

lemma mutation_incarnation_decodes :
  decode_operation mutation_incarnation_operation.`so_raw =
    Some mutation_incarnation_envelope.
proof. by rewrite /mutation_incarnation_operation /mutation_signed_operation. qed.

lemma mutation_incarnation_canonical :
  canonical_reencoding mutation_incarnation_operation.`so_raw.
proof. by rewrite /mutation_incarnation_operation /mutation_signed_operation. qed.

lemma mutation_incarnation_production_rejects :
  ! base_facts_edit_decoded_accepts Production mutation_incarnation_operation
      mutation_incarnation_envelope witness_base_view_exact
      witness_base_state_exact.
proof.
  rewrite /base_facts_edit_decoded_accepts /base_facts_common_accepts.
  smt(bob_new_member_inactive_production).
qed.

lemma mutation_incarnation_removed_accepts :
  base_facts_edit_decoded_accepts
    (WithoutDefense DefenseIncarnationBinding)
    mutation_incarnation_operation mutation_incarnation_envelope
    witness_base_view_exact witness_base_state_exact.
proof.
  rewrite /base_facts_edit_decoded_accepts /base_facts_common_accepts
    /mutation_incarnation_operation /mutation_signed_operation
    /mutation_incarnation_envelope /witness_edit_envelope /defense_enabled.
  rewrite base_singleton_predecessors_exist base_singleton_exact_closure
    witness_base_view_facts witness_base_fact_ids
    witness_base_view_observed_fact_ids base_document_is_witness_document
    bob_new_member_active_without_incarnation
    bob_new_edit_active_without_incarnation edit_body_one_required_capability.
  have Hfresh := base_any_fresh (OperationId 203) (Nonce 203).
  rewrite /operation_signature_message /operation_transcript /defense_enabled.
  smt(edit_body_one_valid).
qed.

lemma mutation_incarnation_wins_probability_one &m :
  Pr[CheckedMutationRunner.run(
       DefenseIncarnationBinding, mutation_incarnation_operation,
       witness_base_view_exact, witness_base_state_exact) @ &m :
     res = (true, 1)] = 1%r.
proof.
  byphoare
    (: removed = DefenseIncarnationBinding
       /\ operation = mutation_incarnation_operation
       /\ view = witness_base_view_exact
       /\ state = witness_base_state_exact
       ==> res = (true, 1)) => //.
  + conseq (base_facts_edit_mutation_run_wins
      DefenseIncarnationBinding mutation_incarnation_operation
      mutation_incarnation_envelope witness_base_view_exact
      witness_base_state_exact) => //.
    + exact witness_base_view_facts.
    + exact witness_base_state_creator.
    + exact mutation_incarnation_decodes.
    + by rewrite /mutation_incarnation_envelope /witness_edit_envelope.
    + exact mutation_incarnation_canonical.
    + exact mutation_incarnation_production_rejects.
    + exact mutation_incarnation_removed_accepts.
  + conseq checked_mutation_runner_lossless => //.
qed.

op mutation_document_envelope : operation_envelope =
  witness_edit_envelope
    (ProtocolDomain 1) 1 witness_other_document (OperationId 204)
    witness_bob_old CapEdit (fset1 witness_base_node)
    (authorization_digest_of witness_authorization_state_7)
    witness_edit_body_one (Nonce 204).

op mutation_document_operation : signed_operation =
  mutation_signed_operation Production mutation_document_envelope
    witness_bob_old.`p_verification_key.

lemma mutation_document_decodes :
  decode_operation mutation_document_operation.`so_raw =
    Some mutation_document_envelope.
proof. by rewrite /mutation_document_operation /mutation_signed_operation. qed.

lemma mutation_document_canonical :
  canonical_reencoding mutation_document_operation.`so_raw.
proof. by rewrite /mutation_document_operation /mutation_signed_operation. qed.

lemma mutation_document_production_rejects :
  ! base_facts_edit_decoded_accepts Production mutation_document_operation
      mutation_document_envelope witness_base_view_exact
      witness_base_state_exact.
proof.
  rewrite /base_facts_edit_decoded_accepts /base_facts_common_accepts
    /mutation_document_envelope /witness_edit_envelope
    base_document_is_witness_document /witness_document
    /witness_other_document /defense_enabled.
  smt().
qed.

lemma mutation_document_removed_accepts :
  base_facts_edit_decoded_accepts
    (WithoutDefense DefenseDocumentBinding)
    mutation_document_operation mutation_document_envelope
    witness_base_view_exact witness_base_state_exact.
proof.
  rewrite /base_facts_edit_decoded_accepts /base_facts_common_accepts
    /mutation_document_operation /mutation_signed_operation
    /mutation_document_envelope /witness_edit_envelope /defense_enabled.
  rewrite base_singleton_predecessors_exist base_singleton_exact_closure
    witness_base_view_facts witness_base_fact_ids
    witness_base_view_observed_fact_ids
    witness_bob_old_member_active_state_7
    witness_bob_old_edit_active_state_7 edit_body_one_required_capability.
  have Hfresh := base_any_fresh (OperationId 204) (Nonce 204).
  rewrite /operation_signature_message /operation_transcript /defense_enabled.
  smt(edit_body_one_valid).
qed.

lemma mutation_document_wins_probability_one &m :
  Pr[CheckedMutationRunner.run(
       DefenseDocumentBinding, mutation_document_operation,
       witness_base_view_exact, witness_base_state_exact) @ &m :
     res = (true, 1)] = 1%r.
proof.
  byphoare
    (: removed = DefenseDocumentBinding
       /\ operation = mutation_document_operation
       /\ view = witness_base_view_exact
       /\ state = witness_base_state_exact
       ==> res = (true, 1)) => //.
  + conseq (base_facts_edit_mutation_run_wins
      DefenseDocumentBinding mutation_document_operation
      mutation_document_envelope witness_base_view_exact
      witness_base_state_exact) => //.
    + exact witness_base_view_facts.
    + exact witness_base_state_creator.
    + exact mutation_document_decodes.
    + by rewrite /mutation_document_envelope /witness_edit_envelope.
    + exact mutation_document_canonical.
    + exact mutation_document_production_rejects.
    + exact mutation_document_removed_accepts.
  + conseq checked_mutation_runner_lossless => //.
qed.

op mutation_domain_envelope : operation_envelope =
  witness_edit_envelope
    (ProtocolDomain 2) 2 witness_document (OperationId 205)
    witness_bob_old CapEdit (fset1 witness_base_node)
    (authorization_digest_of witness_authorization_state_7)
    witness_edit_body_one (Nonce 205).

op mutation_domain_operation : signed_operation =
  mutation_signed_operation Production mutation_domain_envelope
    witness_bob_old.`p_verification_key.

lemma mutation_domain_decodes :
  decode_operation mutation_domain_operation.`so_raw =
    Some mutation_domain_envelope.
proof. by rewrite /mutation_domain_operation /mutation_signed_operation. qed.

lemma mutation_domain_canonical :
  canonical_reencoding mutation_domain_operation.`so_raw.
proof. by rewrite /mutation_domain_operation /mutation_signed_operation. qed.

lemma mutation_domain_production_rejects :
  ! base_facts_edit_decoded_accepts Production mutation_domain_operation
      mutation_domain_envelope witness_base_view_exact
      witness_base_state_exact.
proof.
  rewrite /base_facts_edit_decoded_accepts /base_facts_common_accepts
    /mutation_domain_envelope /witness_edit_envelope
    /expected_protocol_domain /expected_protocol_version /defense_enabled.
  smt().
qed.

lemma mutation_domain_removed_accepts :
  base_facts_edit_decoded_accepts
    (WithoutDefense DefenseDomainVersion)
    mutation_domain_operation mutation_domain_envelope
    witness_base_view_exact witness_base_state_exact.
proof.
  rewrite /base_facts_edit_decoded_accepts /base_facts_common_accepts
    /mutation_domain_operation /mutation_signed_operation
    /mutation_domain_envelope /witness_edit_envelope /defense_enabled.
  rewrite base_singleton_predecessors_exist base_singleton_exact_closure
    witness_base_view_facts witness_base_fact_ids
    witness_base_view_observed_fact_ids base_document_is_witness_document
    witness_bob_old_member_active_state_7
    witness_bob_old_edit_active_state_7 edit_body_one_required_capability.
  have Hfresh := base_any_fresh (OperationId 205) (Nonce 205).
  rewrite /operation_signature_message /operation_transcript /defense_enabled.
  smt(edit_body_one_valid).
qed.

lemma mutation_domain_wins_probability_one &m :
  Pr[CheckedMutationRunner.run(
       DefenseDomainVersion, mutation_domain_operation,
       witness_base_view_exact, witness_base_state_exact) @ &m :
     res = (true, 1)] = 1%r.
proof.
  byphoare
    (: removed = DefenseDomainVersion
       /\ operation = mutation_domain_operation
       /\ view = witness_base_view_exact
       /\ state = witness_base_state_exact
       ==> res = (true, 1)) => //.
  + conseq (base_facts_edit_mutation_run_wins
      DefenseDomainVersion mutation_domain_operation
      mutation_domain_envelope witness_base_view_exact
      witness_base_state_exact) => //.
    + exact witness_base_view_facts.
    + exact witness_base_state_creator.
    + exact mutation_domain_decodes.
    + by rewrite /mutation_domain_envelope /witness_edit_envelope.
    + exact mutation_domain_canonical.
    + exact mutation_domain_production_rejects.
    + exact mutation_domain_removed_accepts.
  + conseq checked_mutation_runner_lossless => //.
qed.
