require import AllCore List FSet.
require import ProtocolTypes CanonicalEncoding ProtocolPrimitives AuthorizationState.
require import ProtocolChecks ProtocolOracles WitnessFixtures MutationWitnesses.
require import AuthorizationWitnessTrace HonestOperationContract.
require import ValidatorCharacterization MutationGameProofs MutationEditProofs.

lemma edit_body_two_required_capability :
  required_capability_for_operation OpEdit witness_edit_body_two = CapEdit.
proof. by rewrite /witness_edit_body_two /required_capability_for_operation
  /required_capability_for_edit_body. qed.

lemma edit_body_two_valid :
  operation_body_valid_for_envelope
    (witness_edit_envelope
      (ProtocolDomain 1) 1 witness_document (OperationId 1)
      witness_bob_old CapEdit (fset1 witness_base_node)
      (authorization_digest_of witness_authorization_state_7)
      witness_edit_body_two (Nonce 1)).
proof.
  by rewrite /witness_edit_envelope /witness_edit_body_two
    /operation_body_valid_for_envelope /operation_body_kind
    /operation_body_valid.
qed.

lemma delete_body_valid :
  operation_body_valid_for_envelope
    (witness_edit_envelope
      (ProtocolDomain 1) 1 witness_document (OperationId 1)
      witness_bob_old CapEdit (fset1 witness_base_node)
      (authorization_digest_of witness_authorization_state_7)
      witness_delete_body (Nonce 1)).
proof.
  by rewrite /witness_edit_envelope /witness_delete_body
    /operation_body_valid_for_envelope /operation_body_kind
    /operation_body_valid.
qed.

lemma delete_body_requires_admin :
  required_capability_for_operation OpEdit witness_delete_body = CapAdmin.
proof.
  by rewrite /witness_delete_body /required_capability_for_operation
    /required_capability_for_edit_body.
qed.

op mutation_body_envelope : operation_envelope =
  witness_edit_envelope
    (ProtocolDomain 1) 1 witness_document (OperationId 206)
    witness_bob_old CapEdit (fset1 witness_base_node)
    (authorization_digest_of witness_authorization_state_7)
    witness_edit_body_two (Nonce 206).

op mutation_body_operation : signed_operation =
  mutation_signed_operation
    (WithoutDefense DefenseOperationBodyBinding)
    mutation_body_envelope witness_bob_old.`p_verification_key.

lemma mutation_body_decodes :
  decode_operation mutation_body_operation.`so_raw = Some mutation_body_envelope.
proof. by rewrite /mutation_body_operation /mutation_signed_operation. qed.

lemma mutation_body_canonical :
  canonical_reencoding mutation_body_operation.`so_raw.
proof. by rewrite /mutation_body_operation /mutation_signed_operation. qed.

lemma mutation_body_production_rejects :
  ! base_facts_edit_decoded_accepts Production mutation_body_operation
      mutation_body_envelope witness_base_view_exact witness_base_state_exact.
proof.
  rewrite /base_facts_edit_decoded_accepts /base_facts_common_accepts
    /mutation_body_operation /mutation_signed_operation
    /mutation_body_envelope /witness_edit_envelope
    /operation_signature_message /operation_transcript /defense_enabled.
  smt().
qed.

lemma mutation_body_removed_accepts :
  base_facts_edit_decoded_accepts
    (WithoutDefense DefenseOperationBodyBinding)
    mutation_body_operation mutation_body_envelope
    witness_base_view_exact witness_base_state_exact.
proof.
  rewrite /base_facts_edit_decoded_accepts /base_facts_common_accepts
    /mutation_body_operation /mutation_signed_operation
    /mutation_body_envelope /witness_edit_envelope /defense_enabled.
  rewrite base_singleton_predecessors_exist base_singleton_exact_closure
    witness_base_view_facts witness_base_fact_ids
    witness_base_view_observed_fact_ids base_document_is_witness_document
    witness_bob_old_member_active_state_7
    witness_bob_old_edit_active_state_7 edit_body_two_required_capability.
  have Hfresh := base_any_fresh (OperationId 206) (Nonce 206).
  rewrite /operation_signature_message /operation_transcript /defense_enabled.
  smt(edit_body_two_valid).
qed.

lemma mutation_body_wins_probability_one &m :
  Pr[CheckedMutationRunner.run(
       DefenseOperationBodyBinding, mutation_body_operation,
       witness_base_view_exact, witness_base_state_exact) @ &m :
     res = (true, 1)] = 1%r.
proof.
  byphoare
    (: removed = DefenseOperationBodyBinding
       /\ operation = mutation_body_operation
       /\ view = witness_base_view_exact
       /\ state = witness_base_state_exact
       ==> res = (true, 1)) => //.
  + conseq (base_facts_edit_mutation_run_wins
      DefenseOperationBodyBinding mutation_body_operation
      mutation_body_envelope witness_base_view_exact
      witness_base_state_exact) => //.
    + exact witness_base_view_facts.
    + exact witness_base_state_creator.
    + exact mutation_body_decodes.
    + by rewrite /mutation_body_envelope /witness_edit_envelope.
    + exact mutation_body_canonical.
    + exact mutation_body_production_rejects.
    + exact mutation_body_removed_accepts.
  + conseq checked_mutation_runner_lossless => //.
qed.

op mutation_capability_envelope : operation_envelope =
  witness_edit_envelope
    (ProtocolDomain 1) 1 witness_document (OperationId 207)
    witness_bob_old CapEdit (fset1 witness_base_node)
    (authorization_digest_of witness_authorization_state_7)
    witness_delete_body (Nonce 207).

op mutation_capability_operation : signed_operation =
  mutation_signed_operation
    (WithoutDefense DefenseRequiredCapabilityBinding)
    mutation_capability_envelope witness_bob_old.`p_verification_key.

lemma mutation_capability_decodes :
  decode_operation mutation_capability_operation.`so_raw =
    Some mutation_capability_envelope.
proof. by rewrite /mutation_capability_operation /mutation_signed_operation. qed.

lemma mutation_capability_canonical :
  canonical_reencoding mutation_capability_operation.`so_raw.
proof. by rewrite /mutation_capability_operation /mutation_signed_operation. qed.

lemma mutation_capability_production_rejects :
  ! base_facts_edit_decoded_accepts Production mutation_capability_operation
      mutation_capability_envelope witness_base_view_exact
      witness_base_state_exact.
proof.
  rewrite /base_facts_edit_decoded_accepts /base_facts_common_accepts
    /mutation_capability_operation /mutation_signed_operation
    /mutation_capability_envelope /witness_edit_envelope
    /operation_signature_message /operation_transcript /defense_enabled.
  smt(delete_body_requires_admin).
qed.

lemma mutation_capability_removed_accepts :
  base_facts_edit_decoded_accepts
    (WithoutDefense DefenseRequiredCapabilityBinding)
    mutation_capability_operation mutation_capability_envelope
    witness_base_view_exact witness_base_state_exact.
proof.
  rewrite /base_facts_edit_decoded_accepts /base_facts_common_accepts
    /mutation_capability_operation /mutation_signed_operation
    /mutation_capability_envelope /witness_edit_envelope /defense_enabled.
  rewrite base_singleton_predecessors_exist base_singleton_exact_closure
    witness_base_view_facts witness_base_fact_ids
    witness_base_view_observed_fact_ids base_document_is_witness_document
    witness_bob_old_member_active_state_7
    witness_bob_old_edit_active_state_7.
  have Hfresh := base_any_fresh (OperationId 207) (Nonce 207).
  rewrite /operation_signature_message /operation_transcript /defense_enabled.
  smt(delete_body_valid).
qed.

lemma mutation_capability_wins_probability_one &m :
  Pr[CheckedMutationRunner.run(
       DefenseRequiredCapabilityBinding, mutation_capability_operation,
       witness_base_view_exact, witness_base_state_exact) @ &m :
     res = (true, 1)] = 1%r.
proof.
  byphoare
    (: removed = DefenseRequiredCapabilityBinding
       /\ operation = mutation_capability_operation
       /\ view = witness_base_view_exact
       /\ state = witness_base_state_exact
       ==> res = (true, 1)) => //.
  + conseq (base_facts_edit_mutation_run_wins
      DefenseRequiredCapabilityBinding mutation_capability_operation
      mutation_capability_envelope witness_base_view_exact
      witness_base_state_exact) => //.
    + exact witness_base_view_facts.
    + exact witness_base_state_creator.
    + exact mutation_capability_decodes.
    + by rewrite /mutation_capability_envelope /witness_edit_envelope.
    + exact mutation_capability_canonical.
    + exact mutation_capability_production_rejects.
    + exact mutation_capability_removed_accepts.
  + conseq checked_mutation_runner_lossless => //.
qed.

op mutation_context_view : public_view =
  witness_public_view witness_base_signed_facts witness_context_6.

op mutation_context_envelope : operation_envelope =
  witness_edit_envelope
    (ProtocolDomain 1) 1 witness_document (OperationId 208)
    witness_bob_old CapEdit (fset1 witness_base_node)
    (authorization_digest_of witness_authorization_state_7)
    witness_edit_body_one (Nonce 208).

op mutation_context_operation : signed_operation =
  mutation_signed_operation Production mutation_context_envelope
    witness_bob_old.`p_verification_key.

lemma mutation_context_view_facts :
  mutation_context_view.`pv_facts = witness_base_signed_facts.
proof. by rewrite /mutation_context_view /witness_public_view. qed.

lemma mutation_context_decodes :
  decode_operation mutation_context_operation.`so_raw = Some mutation_context_envelope.
proof. by rewrite /mutation_context_operation /mutation_signed_operation. qed.

lemma mutation_context_canonical : canonical_reencoding mutation_context_operation.`so_raw.
proof. by rewrite /mutation_context_operation /mutation_signed_operation. qed.

lemma mutation_context_production_rejects :
  ! base_facts_edit_decoded_accepts Production mutation_context_operation
      mutation_context_envelope mutation_context_view witness_base_state_exact.
proof.
  rewrite /base_facts_edit_decoded_accepts /base_facts_common_accepts
    /mutation_context_view /witness_public_view
    witness_base_fact_ids /witness_context_6 /witness_context_7
    /witness_fact_id_7 /defense_enabled.
  smt(in_fsetU in_fset1).
qed.

lemma mutation_context_removed_accepts :
  base_facts_edit_decoded_accepts
    (WithoutDefense DefenseExactCausalContext)
    mutation_context_operation mutation_context_envelope
    mutation_context_view witness_base_state_exact.
proof.
  rewrite /base_facts_edit_decoded_accepts /base_facts_common_accepts
    /mutation_context_operation /mutation_signed_operation
    /mutation_context_envelope /witness_edit_envelope
    /mutation_context_view /witness_public_view /defense_enabled.
  rewrite base_singleton_predecessors_exist base_singleton_exact_closure
    witness_base_fact_ids base_document_is_witness_document
    witness_bob_old_member_active_state_7
    witness_bob_old_edit_active_state_7 edit_body_one_required_capability.
  have Hfresh := base_any_fresh (OperationId 208) (Nonce 208).
  rewrite /operation_signature_message /operation_transcript /defense_enabled.
  smt(edit_body_one_valid).
qed.

lemma mutation_context_wins_probability_one &m :
  Pr[CheckedMutationRunner.run(
       DefenseExactCausalContext, mutation_context_operation,
       mutation_context_view, witness_base_state_exact) @ &m :
     res = (true, 1)] = 1%r.
proof.
  byphoare
    (: removed = DefenseExactCausalContext
       /\ operation = mutation_context_operation
       /\ view = mutation_context_view
       /\ state = witness_base_state_exact
       ==> res = (true, 1)) => //.
  + conseq (base_facts_edit_mutation_run_wins
      DefenseExactCausalContext mutation_context_operation
      mutation_context_envelope mutation_context_view
      witness_base_state_exact) => //.
    + exact mutation_context_view_facts.
    + exact witness_base_state_creator.
    + exact mutation_context_decodes.
    + by rewrite /mutation_context_envelope /witness_edit_envelope.
    + exact mutation_context_canonical.
    + exact mutation_context_production_rejects.
    + exact mutation_context_removed_accepts.
  + conseq checked_mutation_runner_lossless => //.
qed.

op mutation_digest_envelope : operation_envelope =
  witness_edit_envelope
    (ProtocolDomain 1) 1 witness_document (OperationId 209)
    witness_bob_old CapEdit (fset1 witness_base_node)
    (InvalidAuthorizationDigest 7) witness_edit_body_one (Nonce 209).

op mutation_digest_operation : signed_operation =
  mutation_signed_operation Production mutation_digest_envelope
    witness_bob_old.`p_verification_key.

lemma mutation_digest_decodes :
  decode_operation mutation_digest_operation.`so_raw = Some mutation_digest_envelope.
proof. by rewrite /mutation_digest_operation /mutation_signed_operation. qed.

lemma mutation_digest_canonical : canonical_reencoding mutation_digest_operation.`so_raw.
proof. by rewrite /mutation_digest_operation /mutation_signed_operation. qed.

lemma mutation_digest_production_rejects :
  ! base_facts_edit_decoded_accepts Production mutation_digest_operation
      mutation_digest_envelope witness_base_view_exact witness_base_state_exact.
proof.
  rewrite /base_facts_edit_decoded_accepts /base_facts_common_accepts
    /mutation_digest_envelope /witness_edit_envelope /defense_enabled.
  smt().
qed.

lemma mutation_digest_removed_accepts :
  base_facts_edit_decoded_accepts
    (WithoutDefense DefenseAuthorizationDigest)
    mutation_digest_operation mutation_digest_envelope
    witness_base_view_exact witness_base_state_exact.
proof.
  rewrite /base_facts_edit_decoded_accepts /base_facts_common_accepts
    /mutation_digest_operation /mutation_signed_operation
    /mutation_digest_envelope /witness_edit_envelope /defense_enabled.
  rewrite base_singleton_predecessors_exist base_singleton_exact_closure
    witness_base_view_facts witness_base_fact_ids
    witness_base_view_observed_fact_ids base_document_is_witness_document
    witness_bob_old_member_active_state_7
    witness_bob_old_edit_active_state_7 edit_body_one_required_capability.
  have Hfresh := base_any_fresh (OperationId 209) (Nonce 209).
  rewrite /operation_signature_message /operation_transcript /defense_enabled.
  smt(edit_body_one_valid).
qed.

lemma mutation_digest_wins_probability_one &m :
  Pr[CheckedMutationRunner.run(
       DefenseAuthorizationDigest, mutation_digest_operation,
       witness_base_view_exact, witness_base_state_exact) @ &m :
     res = (true, 1)] = 1%r.
proof.
  byphoare
    (: removed = DefenseAuthorizationDigest
       /\ operation = mutation_digest_operation
       /\ view = witness_base_view_exact
       /\ state = witness_base_state_exact
       ==> res = (true, 1)) => //.
  + conseq (base_facts_edit_mutation_run_wins
      DefenseAuthorizationDigest mutation_digest_operation
      mutation_digest_envelope witness_base_view_exact
      witness_base_state_exact) => //.
    + exact witness_base_view_facts.
    + exact witness_base_state_creator.
    + exact mutation_digest_decodes.
    + by rewrite /mutation_digest_envelope /witness_edit_envelope.
    + exact mutation_digest_canonical.
    + exact mutation_digest_production_rejects.
    + exact mutation_digest_removed_accepts.
  + conseq checked_mutation_runner_lossless => //.
qed.

op mutation_predecessor_state : protocol_state =
  witness_protocol_state witness_missing_revoke_node witness_context_8.

op mutation_predecessor_view : public_view =
  witness_public_view witness_base_signed_facts witness_context_7.

op mutation_predecessor_envelope : operation_envelope =
  witness_edit_envelope
    (ProtocolDomain 1) 1 witness_document (OperationId 210)
    witness_bob_old CapEdit (fset1 witness_missing_revoke_node)
    (authorization_digest_of witness_authorization_state_7)
    witness_edit_body_one (Nonce 210).

op mutation_predecessor_operation : signed_operation =
  mutation_signed_operation Production mutation_predecessor_envelope
    witness_bob_old.`p_verification_key.

lemma mutation_predecessor_view_facts :
  mutation_predecessor_view.`pv_facts = witness_base_signed_facts.
proof. by rewrite /mutation_predecessor_view /witness_public_view. qed.

lemma mutation_predecessor_state_creator :
  mutation_predecessor_state.`ps_creator = witness_alice.
proof. by rewrite /mutation_predecessor_state /witness_protocol_state. qed.

lemma mutation_predecessor_decodes :
  decode_operation mutation_predecessor_operation.`so_raw =
    Some mutation_predecessor_envelope.
proof. by rewrite /mutation_predecessor_operation /mutation_signed_operation. qed.

lemma mutation_predecessor_canonical :
  canonical_reencoding mutation_predecessor_operation.`so_raw.
proof. by rewrite /mutation_predecessor_operation /mutation_signed_operation. qed.

lemma mutation_predecessor_exists :
  all_predecessors_exist mutation_predecessor_state
    (fset1 witness_missing_revoke_node).
proof.
  rewrite /all_predecessors_exist (elems_fset1 witness_missing_revoke_node)
    /mutation_predecessor_state /witness_protocol_state /=.
  by rewrite in_fset1.
qed.

lemma mutation_predecessor_closure :
  exact_predecessor_closure mutation_predecessor_state
    (fset1 witness_missing_revoke_node) = Some witness_context_8.
proof.
  rewrite /exact_predecessor_closure (elems_fset1 witness_missing_revoke_node)
    /mutation_predecessor_state /witness_protocol_state
    /witness_closure_map /=.
  by rewrite fsetU0.
qed.

lemma mutation_predecessor_production_rejects :
  ! base_facts_edit_decoded_accepts Production mutation_predecessor_operation
      mutation_predecessor_envelope mutation_predecessor_view
      mutation_predecessor_state.
proof.
  rewrite /base_facts_edit_decoded_accepts /base_facts_common_accepts
    /mutation_predecessor_envelope /witness_edit_envelope
    mutation_predecessor_closure mutation_predecessor_view_facts
    witness_base_fact_ids /witness_context_8 /defense_enabled.
  smt(in_fsetU in_fset1).
qed.

lemma mutation_predecessor_removed_accepts :
  base_facts_edit_decoded_accepts
    (WithoutDefense DefensePredecessorCompleteness)
    mutation_predecessor_operation mutation_predecessor_envelope
    mutation_predecessor_view mutation_predecessor_state.
proof.
  rewrite /base_facts_edit_decoded_accepts /base_facts_common_accepts
    /mutation_predecessor_operation /mutation_signed_operation
    /mutation_predecessor_envelope /witness_edit_envelope
    /mutation_predecessor_view /witness_public_view
    /mutation_predecessor_state /witness_protocol_state /defense_enabled.
  rewrite mutation_predecessor_exists witness_base_fact_ids
    witness_bob_old_member_active_state_7
    witness_bob_old_edit_active_state_7 edit_body_one_required_capability.
  rewrite /operation_signature_message /operation_transcript /defense_enabled.
  smt(edit_body_one_valid in_fset0).
qed.

lemma mutation_predecessor_wins_probability_one &m :
  Pr[CheckedMutationRunner.run(
       DefensePredecessorCompleteness, mutation_predecessor_operation,
       mutation_predecessor_view, mutation_predecessor_state) @ &m :
     res = (true, 1)] = 1%r.
proof.
  byphoare
    (: removed = DefensePredecessorCompleteness
       /\ operation = mutation_predecessor_operation
       /\ view = mutation_predecessor_view
       /\ state = mutation_predecessor_state
       ==> res = (true, 1)) => //.
  + conseq (base_facts_edit_mutation_run_wins
      DefensePredecessorCompleteness mutation_predecessor_operation
      mutation_predecessor_envelope mutation_predecessor_view
      mutation_predecessor_state) => //.
    + exact mutation_predecessor_view_facts.
    + exact mutation_predecessor_state_creator.
    + exact mutation_predecessor_decodes.
    + by rewrite /mutation_predecessor_envelope /witness_edit_envelope.
    + exact mutation_predecessor_canonical.
    + exact mutation_predecessor_production_rejects.
    + exact mutation_predecessor_removed_accepts.
  + conseq checked_mutation_runner_lossless => //.
qed.
