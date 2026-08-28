require import AllCore List FSet.
require import ProtocolTypes CanonicalEncoding ProtocolPrimitives AuthorizationState.
require import ProtocolChecks ProtocolOracles WitnessFixtures MutationWitnesses.
require import AuthorizationWitnessTrace HonestOperationContract.
require import ValidatorCharacterization MutationGameProofs MutationEditProofs.

lemma alice_member_active_state_7 :
  member_active Production witness_authorization_state_7 witness_alice.
proof.
  rewrite /member_active /witness_authorization_state_7
    /witness_member_grant_alice_entry /witness_member_grant_bob_old_entry
    /principal_matches /defense_enabled.
  smt(in_fsetU in_fset1 in_fset0).
qed.

lemma alice_history_active_state_7 :
  capability_active Production witness_authorization_state_7
    witness_alice CapHistoryGrant.
proof.
  rewrite /capability_active /witness_authorization_state_7
    /witness_capability_grant_alice_admin_entry
    /witness_capability_grant_alice_history_entry
    /witness_capability_grant_alice_puncture_entry
    /witness_capability_grant_alice_beekem_entry
    /witness_capability_grant_bob_old_edit_entry
    /principal_matches /defense_enabled.
  smt(in_fsetU in_fset1 in_fset0).
qed.

lemma witness_region_valid : region_valid witness_region.
proof.
  rewrite /region_valid /witness_region (elems_fset1 witness_region_interval)
    /region_intervals_valid_list /witness_region_interval.
  trivial.
qed.

lemma witness_enlarged_region_valid : region_valid witness_enlarged_region.
proof.
  rewrite /region_valid /witness_enlarged_region
    (elems_fset1 witness_enlarged_region_interval)
    /region_intervals_valid_list /witness_enlarged_region_interval.
  trivial.
qed.

lemma witness_cover_entries_valid :
  cover_entries_valid_list (elems witness_cover).
proof.
  rewrite /witness_cover (elems_fset1 witness_cover_entry)
    /cover_entries_valid_list /witness_cover_entry.
  trivial.
qed.

lemma witness_cross_cover_entries_valid :
  cover_entries_valid_list (elems witness_cross_segment_cover).
proof.
  rewrite /witness_cross_segment_cover
    (elems_fset1 witness_cross_segment_cover_entry)
    /cover_entries_valid_list /witness_cross_segment_cover_entry.
  trivial.
qed.

lemma witness_cover_valid_for_region :
  cover_valid_for_region witness_cover witness_region.
proof.
  rewrite /cover_valid_for_region /witness_cover
    (elems_fset1 witness_cover_entry)
    /cover_entries_valid_list /cover_segments_within_region_list
    /witness_cover_entry /segment_in_region /witness_region.
  split; first trivial.
  split; last trivial.
  exists witness_region_interval.
  by rewrite in_fset1 /witness_region_interval.
qed.

lemma witness_cross_cover_invalid_for_region :
  ! cover_valid_for_region witness_cross_segment_cover witness_region.
proof.
  rewrite /cover_valid_for_region /witness_cross_segment_cover
    (elems_fset1 witness_cross_segment_cover_entry)
    /cover_entries_valid_list /cover_segments_within_region_list
    /witness_cross_segment_cover_entry /segment_in_region /witness_region.
  smt(in_fset1).
qed.

lemma history_required_capability :
  required_capability_for_operation OpHistoryGrant
    (HistoryGrantBody witness_bob_old witness_merge_node
      witness_region witness_cover) = CapHistoryGrant.
proof. by rewrite /required_capability_for_operation. qed.

lemma history_body_base_valid :
  operation_body_valid_for_envelope
    (witness_history_envelope
      (OperationId 1)
      (authorization_digest_of witness_authorization_state_7)
      witness_bob_old witness_merge_node witness_region witness_cover
      (Nonce 1)).
proof.
  rewrite /witness_history_envelope /operation_body_valid_for_envelope
    /operation_body_kind /operation_body_valid witness_region_valid
    witness_cover_entries_valid.
  trivial.
qed.

lemma history_body_recipient_valid :
  operation_body_valid_for_envelope
    (witness_history_envelope
      (OperationId 1)
      (authorization_digest_of witness_authorization_state_7)
      witness_carol witness_merge_node witness_region witness_cover
      (Nonce 1)).
proof.
  rewrite /witness_history_envelope /operation_body_valid_for_envelope
    /operation_body_kind /operation_body_valid witness_region_valid
    witness_cover_entries_valid.
  trivial.
qed.

lemma history_body_merge_valid :
  operation_body_valid_for_envelope
    (witness_history_envelope
      (OperationId 1)
      (authorization_digest_of witness_authorization_state_7)
      witness_bob_old witness_other_merge_node witness_region witness_cover
      (Nonce 1)).
proof.
  rewrite /witness_history_envelope /operation_body_valid_for_envelope
    /operation_body_kind /operation_body_valid witness_region_valid
    witness_cover_entries_valid.
  trivial.
qed.

lemma history_body_region_valid :
  operation_body_valid_for_envelope
    (witness_history_envelope
      (OperationId 1)
      (authorization_digest_of witness_authorization_state_7)
      witness_bob_old witness_merge_node witness_enlarged_region witness_cover
      (Nonce 1)).
proof.
  rewrite /witness_history_envelope /operation_body_valid_for_envelope
    /operation_body_kind /operation_body_valid witness_enlarged_region_valid
    witness_cover_entries_valid.
  trivial.
qed.

lemma history_body_segment_valid :
  operation_body_valid_for_envelope
    (witness_history_envelope
      (OperationId 1)
      (authorization_digest_of witness_authorization_state_7)
      witness_bob_old witness_merge_node witness_region
      witness_cross_segment_cover (Nonce 1)).
proof.
  rewrite /witness_history_envelope /operation_body_valid_for_envelope
    /operation_body_kind /operation_body_valid witness_region_valid
    witness_cross_cover_entries_valid.
  trivial.
qed.

lemma base_facts_history_differential_submit_wins
    (removed : defense)
    (input_operation : signed_operation)
    (input_envelope : operation_envelope)
    (input_view : public_view)
    (input_state : protocol_state) :
     input_view.`pv_facts = witness_base_signed_facts
  => input_state.`ps_creator = witness_alice
  => decode_operation input_operation.`so_raw = Some input_envelope
  => input_envelope.`oe_operation_kind = OpHistoryGrant
  => canonical_reencoding input_operation.`so_raw
  => ! base_facts_history_decoded_accepts Production input_operation
       input_envelope input_view input_state
  => base_facts_history_decoded_accepts
       (WithoutDefense removed) input_operation input_envelope
       input_view input_state
  => hoare [CheckedMutationRunner.D.submit :
         CheckedMutationRunner.D.removed_defense = removed
      /\ ! CheckedMutationRunner.D.differential_win
      /\ CheckedMutationRunner.D.query_count = 0
      /\ operation = input_operation
      /\ view = input_view
      /\ state = input_state
      ==>
         res
      /\ CheckedMutationRunner.D.differential_win
      /\ CheckedMutationRunner.D.query_count = 1].
proof.
  move=> Hfacts Hcreator Hdecode Hkind Hcanonical Hproduction Hmutated.
  proc.
  call (base_facts_history_validate_characterization
    (WithoutDefense removed) input_operation input_envelope
    input_view input_state).
  call (base_facts_history_validate_characterization
    Production input_operation input_envelope input_view input_state).
  auto=> />.
  smt().
qed.

lemma base_facts_history_mutation_run_wins
    (removed : defense)
    (input_operation : signed_operation)
    (input_envelope : operation_envelope)
    (input_view : public_view)
    (input_state : protocol_state) :
     input_view.`pv_facts = witness_base_signed_facts
  => input_state.`ps_creator = witness_alice
  => decode_operation input_operation.`so_raw = Some input_envelope
  => input_envelope.`oe_operation_kind = OpHistoryGrant
  => canonical_reencoding input_operation.`so_raw
  => ! base_facts_history_decoded_accepts Production input_operation
       input_envelope input_view input_state
  => base_facts_history_decoded_accepts
       (WithoutDefense removed) input_operation input_envelope
       input_view input_state
  => hoare [CheckedMutationRunner.run :
         removed = removed{hr}
      /\ operation = input_operation
      /\ view = input_view
      /\ state = input_state
      ==>
      res = (true, 1)].
proof.
  move=> Hfacts Hcreator Hdecode Hkind Hcanonical Hproduction Hmutated.
  proc.
  inline CheckedMutationRunner.D.init.
  call (base_facts_history_differential_submit_wins
    removed{hr} input_operation input_envelope input_view input_state
    Hfacts Hcreator Hdecode Hkind Hcanonical Hproduction Hmutated).
  auto.
qed.

op mutation_recipient_envelope : operation_envelope =
  witness_history_envelope
    (OperationId 211)
    (authorization_digest_of witness_authorization_state_7)
    witness_carol witness_merge_node witness_region witness_cover (Nonce 211).

op mutation_recipient_operation : signed_operation =
  mutation_signed_operation Production mutation_recipient_envelope
    witness_alice.`p_verification_key.

lemma mutation_recipient_decodes :
  decode_operation mutation_recipient_operation.`so_raw = Some mutation_recipient_envelope.
proof. by rewrite /mutation_recipient_operation /mutation_signed_operation. qed.

lemma mutation_recipient_canonical : canonical_reencoding mutation_recipient_operation.`so_raw.
proof. by rewrite /mutation_recipient_operation /mutation_signed_operation. qed.

lemma mutation_recipient_production_rejects :
  ! base_facts_history_decoded_accepts Production mutation_recipient_operation
      mutation_recipient_envelope witness_base_view_exact witness_base_state_exact.
proof.
  rewrite /base_facts_history_decoded_accepts /mutation_recipient_envelope
    /witness_history_envelope /witness_base_state_exact /witness_protocol_state
    /witness_history_expectation /history_recipient_of_body /defense_enabled.
  smt().
qed.

lemma mutation_recipient_removed_accepts :
  base_facts_history_decoded_accepts
    (WithoutDefense DefenseGrantRecipientBinding)
    mutation_recipient_operation mutation_recipient_envelope
    witness_base_view_exact witness_base_state_exact.
proof.
  rewrite /base_facts_history_decoded_accepts /base_facts_common_accepts
    /mutation_recipient_operation /mutation_signed_operation
    /mutation_recipient_envelope /witness_history_envelope
    /witness_base_state_exact /witness_protocol_state
    /witness_history_expectation /history_recipient_of_body
    /history_merge_node_of_body /history_region_of_body
    /history_cover_of_body /defense_enabled.
  rewrite base_singleton_predecessors_exist base_singleton_exact_closure
    witness_base_view_facts witness_base_fact_ids
    witness_base_view_observed_fact_ids alice_member_active_state_7
    alice_history_active_state_7 witness_cover_valid_for_region.
  have Hfresh := base_any_fresh (OperationId 211) (Nonce 211).
  rewrite /operation_signature_message /operation_transcript /defense_enabled.
  smt(history_body_recipient_valid).
qed.

lemma mutation_recipient_wins_probability_one &m :
  Pr[CheckedMutationRunner.run(
       DefenseGrantRecipientBinding, mutation_recipient_operation,
       witness_base_view_exact, witness_base_state_exact) @ &m :
     res = (true, 1)] = 1%r.
proof.
  byphoare
    (: removed = DefenseGrantRecipientBinding
       /\ operation = mutation_recipient_operation
       /\ view = witness_base_view_exact
       /\ state = witness_base_state_exact
       ==> res = (true, 1)) => //.
  + conseq (base_facts_history_mutation_run_wins
      DefenseGrantRecipientBinding mutation_recipient_operation
      mutation_recipient_envelope witness_base_view_exact
      witness_base_state_exact) => //.
    + exact witness_base_view_facts.
    + exact witness_base_state_creator.
    + exact mutation_recipient_decodes.
    + by rewrite /mutation_recipient_envelope /witness_history_envelope.
    + exact mutation_recipient_canonical.
    + exact mutation_recipient_production_rejects.
    + exact mutation_recipient_removed_accepts.
  + conseq checked_mutation_runner_lossless => //.
qed.

op mutation_merge_envelope : operation_envelope =
  witness_history_envelope
    (OperationId 212)
    (authorization_digest_of witness_authorization_state_7)
    witness_bob_old witness_other_merge_node witness_region witness_cover (Nonce 212).

op mutation_merge_operation : signed_operation =
  mutation_signed_operation Production mutation_merge_envelope
    witness_alice.`p_verification_key.

lemma mutation_merge_decodes :
  decode_operation mutation_merge_operation.`so_raw = Some mutation_merge_envelope.
proof. by rewrite /mutation_merge_operation /mutation_signed_operation. qed.

lemma mutation_merge_canonical : canonical_reencoding mutation_merge_operation.`so_raw.
proof. by rewrite /mutation_merge_operation /mutation_signed_operation. qed.

lemma mutation_merge_production_rejects :
  ! base_facts_history_decoded_accepts Production mutation_merge_operation
      mutation_merge_envelope witness_base_view_exact witness_base_state_exact.
proof.
  rewrite /base_facts_history_decoded_accepts /mutation_merge_envelope
    /witness_history_envelope /witness_base_state_exact /witness_protocol_state
    /witness_history_expectation /history_merge_node_of_body /defense_enabled.
  smt().
qed.

lemma mutation_merge_removed_accepts :
  base_facts_history_decoded_accepts
    (WithoutDefense DefenseMergeNodeBinding)
    mutation_merge_operation mutation_merge_envelope
    witness_base_view_exact witness_base_state_exact.
proof.
  rewrite /base_facts_history_decoded_accepts /base_facts_common_accepts
    /mutation_merge_operation /mutation_signed_operation
    /mutation_merge_envelope /witness_history_envelope
    /witness_base_state_exact /witness_protocol_state
    /witness_history_expectation /history_recipient_of_body
    /history_merge_node_of_body /history_region_of_body
    /history_cover_of_body /defense_enabled.
  rewrite base_singleton_predecessors_exist base_singleton_exact_closure
    witness_base_view_facts witness_base_fact_ids
    witness_base_view_observed_fact_ids alice_member_active_state_7
    alice_history_active_state_7 witness_cover_valid_for_region.
  have Hfresh := base_any_fresh (OperationId 212) (Nonce 212).
  rewrite /operation_signature_message /operation_transcript /defense_enabled.
  smt(history_body_merge_valid).
qed.

lemma mutation_merge_wins_probability_one &m :
  Pr[CheckedMutationRunner.run(
       DefenseMergeNodeBinding, mutation_merge_operation,
       witness_base_view_exact, witness_base_state_exact) @ &m :
     res = (true, 1)] = 1%r.
proof.
  byphoare
    (: removed = DefenseMergeNodeBinding
       /\ operation = mutation_merge_operation
       /\ view = witness_base_view_exact
       /\ state = witness_base_state_exact
       ==> res = (true, 1)) => //.
  + conseq (base_facts_history_mutation_run_wins
      DefenseMergeNodeBinding mutation_merge_operation mutation_merge_envelope
      witness_base_view_exact witness_base_state_exact) => //.
    + exact witness_base_view_facts.
    + exact witness_base_state_creator.
    + exact mutation_merge_decodes.
    + by rewrite /mutation_merge_envelope /witness_history_envelope.
    + exact mutation_merge_canonical.
    + exact mutation_merge_production_rejects.
    + exact mutation_merge_removed_accepts.
  + conseq checked_mutation_runner_lossless => //.
qed.

op mutation_region_envelope : operation_envelope =
  witness_history_envelope
    (OperationId 213)
    (authorization_digest_of witness_authorization_state_7)
    witness_bob_old witness_merge_node witness_enlarged_region witness_cover
    (Nonce 213).

op mutation_region_operation : signed_operation =
  mutation_signed_operation Production mutation_region_envelope
    witness_alice.`p_verification_key.

lemma mutation_region_decodes :
  decode_operation mutation_region_operation.`so_raw = Some mutation_region_envelope.
proof. by rewrite /mutation_region_operation /mutation_signed_operation. qed.

lemma mutation_region_canonical : canonical_reencoding mutation_region_operation.`so_raw.
proof. by rewrite /mutation_region_operation /mutation_signed_operation. qed.

lemma mutation_region_production_rejects :
  ! base_facts_history_decoded_accepts Production mutation_region_operation
      mutation_region_envelope witness_base_view_exact witness_base_state_exact.
proof.
  rewrite /base_facts_history_decoded_accepts /mutation_region_envelope
    /witness_history_envelope /witness_base_state_exact /witness_protocol_state
    /witness_history_expectation /history_region_of_body /defense_enabled.
  smt().
qed.

lemma mutation_region_removed_accepts :
  base_facts_history_decoded_accepts
    (WithoutDefense DefenseRegionBinding)
    mutation_region_operation mutation_region_envelope
    witness_base_view_exact witness_base_state_exact.
proof.
  rewrite /base_facts_history_decoded_accepts /base_facts_common_accepts
    /mutation_region_operation /mutation_signed_operation
    /mutation_region_envelope /witness_history_envelope
    /witness_base_state_exact /witness_protocol_state
    /witness_history_expectation /history_recipient_of_body
    /history_merge_node_of_body /history_region_of_body
    /history_cover_of_body /defense_enabled.
  rewrite base_singleton_predecessors_exist base_singleton_exact_closure
    witness_base_view_facts witness_base_fact_ids
    witness_base_view_observed_fact_ids alice_member_active_state_7
    alice_history_active_state_7.
  have Hfresh := base_any_fresh (OperationId 213) (Nonce 213).
  rewrite /operation_signature_message /operation_transcript /defense_enabled.
  smt(history_body_region_valid witness_cover_valid_for_region).
qed.

lemma mutation_region_wins_probability_one &m :
  Pr[CheckedMutationRunner.run(
       DefenseRegionBinding, mutation_region_operation,
       witness_base_view_exact, witness_base_state_exact) @ &m :
     res = (true, 1)] = 1%r.
proof.
  byphoare
    (: removed = DefenseRegionBinding
       /\ operation = mutation_region_operation
       /\ view = witness_base_view_exact
       /\ state = witness_base_state_exact
       ==> res = (true, 1)) => //.
  + conseq (base_facts_history_mutation_run_wins
      DefenseRegionBinding mutation_region_operation mutation_region_envelope
      witness_base_view_exact witness_base_state_exact) => //.
    + exact witness_base_view_facts.
    + exact witness_base_state_creator.
    + exact mutation_region_decodes.
    + by rewrite /mutation_region_envelope /witness_history_envelope.
    + exact mutation_region_canonical.
    + exact mutation_region_production_rejects.
    + exact mutation_region_removed_accepts.
  + conseq checked_mutation_runner_lossless => //.
qed.

op mutation_segment_envelope : operation_envelope =
  witness_history_envelope
    (OperationId 214)
    (authorization_digest_of witness_authorization_state_7)
    witness_bob_old witness_merge_node witness_region
    witness_cross_segment_cover (Nonce 214).

op mutation_segment_operation : signed_operation =
  mutation_signed_operation Production mutation_segment_envelope
    witness_alice.`p_verification_key.

lemma mutation_segment_decodes :
  decode_operation mutation_segment_operation.`so_raw = Some mutation_segment_envelope.
proof. by rewrite /mutation_segment_operation /mutation_signed_operation. qed.

lemma mutation_segment_canonical : canonical_reencoding mutation_segment_operation.`so_raw.
proof. by rewrite /mutation_segment_operation /mutation_signed_operation. qed.

lemma mutation_segment_production_rejects :
  ! base_facts_history_decoded_accepts Production mutation_segment_operation
      mutation_segment_envelope witness_base_view_exact witness_base_state_exact.
proof.
  rewrite /base_facts_history_decoded_accepts /mutation_segment_envelope
    /witness_history_envelope /witness_base_state_exact /witness_protocol_state
    /witness_history_expectation /history_cover_of_body /defense_enabled.
  smt(witness_cross_cover_invalid_for_region).
qed.

lemma mutation_segment_removed_accepts :
  base_facts_history_decoded_accepts
    (WithoutDefense DefenseSegmentBinding)
    mutation_segment_operation mutation_segment_envelope
    witness_base_view_exact witness_base_state_exact.
proof.
  rewrite /base_facts_history_decoded_accepts /base_facts_common_accepts
    /mutation_segment_operation /mutation_signed_operation
    /mutation_segment_envelope /witness_history_envelope
    /witness_base_state_exact /witness_protocol_state
    /witness_history_expectation /history_recipient_of_body
    /history_merge_node_of_body /history_region_of_body
    /history_cover_of_body /defense_enabled.
  rewrite base_singleton_predecessors_exist base_singleton_exact_closure
    witness_base_view_facts witness_base_fact_ids
    witness_base_view_observed_fact_ids alice_member_active_state_7
    alice_history_active_state_7.
  have Hfresh := base_any_fresh (OperationId 214) (Nonce 214).
  rewrite /operation_signature_message /operation_transcript /defense_enabled.
  smt(history_body_segment_valid).
qed.

lemma mutation_segment_wins_probability_one &m :
  Pr[CheckedMutationRunner.run(
       DefenseSegmentBinding, mutation_segment_operation,
       witness_base_view_exact, witness_base_state_exact) @ &m :
     res = (true, 1)] = 1%r.
proof.
  byphoare
    (: removed = DefenseSegmentBinding
       /\ operation = mutation_segment_operation
       /\ view = witness_base_view_exact
       /\ state = witness_base_state_exact
       ==> res = (true, 1)) => //.
  + conseq (base_facts_history_mutation_run_wins
      DefenseSegmentBinding mutation_segment_operation mutation_segment_envelope
      witness_base_view_exact witness_base_state_exact) => //.
    + exact witness_base_view_facts.
    + exact witness_base_state_creator.
    + exact mutation_segment_decodes.
    + by rewrite /mutation_segment_envelope /witness_history_envelope.
    + exact mutation_segment_canonical.
    + exact mutation_segment_production_rejects.
    + exact mutation_segment_removed_accepts.
  + conseq checked_mutation_runner_lossless => //.
qed.
