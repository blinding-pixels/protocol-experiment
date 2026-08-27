require import AllCore List FSet.
require import ProtocolTypes CanonicalEncoding ProtocolPrimitives AuthorizationState.
require import WitnessFixtures AuthorizationWitnessTrace.

(* Remaining concrete steps of the honest seven-fact authorization ledger. *)

lemma witness_fact_4_shape_valid :
  authorization_fact_shape_valid witness_fact_4.
proof.
  by rewrite /authorization_fact_shape_valid
    /authorization_fact_shape_valid_kind /witness_fact_4.
qed.

lemma witness_fact_4_id_fresh :
  witness_fact_4.`af_id \notin witness_authorization_state_3.`as_fact_ids.
proof.
  rewrite /witness_fact_4 /witness_authorization_state_3
    /witness_context_3 /witness_context_2 /witness_context_1
    /witness_fact_id_1 /witness_fact_id_2 /witness_fact_id_3
    /witness_fact_id_4.
  smt(in_fsetU in_fset1).
qed.

lemma witness_alice_active_state_3 :
  member_active Production witness_authorization_state_3 witness_alice.
proof.
  rewrite /member_active /witness_authorization_state_3
    /witness_member_grant_alice_entry /principal_matches /defense_enabled.
  smt(in_fset1 in_fset0).
qed.

lemma witness_fact_4_issuer_allowed :
  authorization_issuer_allowed
    witness_authorization_state_3
    witness_authorization_state_3
    witness_alice
    witness_fact_4.
proof.
  by rewrite /authorization_issuer_allowed /genesis_authorization_fact
    /witness_fact_4 witness_alice_active_state_3.
qed.

lemma witness_puncture_tag_unknown_state_3 :
  capability_tag_known
    witness_authorization_state_3
    witness_capability_tag_alice_puncture = false.
proof.
  rewrite /capability_tag_known /witness_authorization_state_3
    /witness_capability_grant_alice_admin_entry
    /witness_capability_grant_alice_history_entry
    /witness_capability_tag_alice_admin
    /witness_capability_tag_alice_history
    /witness_capability_tag_alice_puncture.
  smt(in_fsetU in_fset1).
qed.

lemma witness_fact_4_kind_application :
  apply_authorization_fact_kind
    witness_fact_4.`af_kind
    witness_authorization_state_3
    witness_fact_4 =
  Some witness_authorization_state_4.
proof.
  rewrite /apply_authorization_fact_kind /witness_fact_4
    /witness_authorization_state_3 /witness_authorization_state_4
    /witness_capability_grant_alice_admin_entry
    /witness_capability_grant_alice_history_entry
    /witness_capability_grant_alice_puncture_entry
    /witness_capability_tag_alice_admin
    /witness_capability_tag_alice_history
    /witness_capability_tag_alice_puncture
    /witness_context_4 /capability_tag_known;
  cbv delta;
  by smt(in_fsetU in_fset1).
qed.

lemma witness_fact_4_transition :
  apply_authorization_fact
    witness_authorization_state_3
    witness_authorization_state_3
    witness_alice
    witness_fact_4 =
  Some witness_authorization_state_4.
proof.
  rewrite /apply_authorization_fact witness_fact_4_shape_valid
    witness_fact_4_id_fresh witness_fact_4_issuer_allowed.
  exact witness_fact_4_kind_application.
qed.

lemma witness_fact_5_transition :
  apply_authorization_fact
    witness_authorization_state_4
    witness_authorization_state_4
    witness_alice
    witness_fact_5 =
  Some witness_authorization_state_5.
proof.
  rewrite /witness_authorization_state_4 /witness_authorization_state_5
    /witness_member_grant_alice_entry
    /witness_capability_grant_alice_admin_entry
    /witness_capability_grant_alice_history_entry
    /witness_capability_grant_alice_puncture_entry
    /witness_capability_grant_alice_beekem_entry
    /witness_fact_5 /witness_context_1 /witness_context_2
    /witness_context_3 /witness_context_4 /witness_context_5
    /witness_alice /witness_capability_tag_alice_admin
    /witness_capability_tag_alice_history
    /witness_capability_tag_alice_puncture
    /witness_capability_tag_alice_beekem
    /witness_fact_id_1 /witness_fact_id_2 /witness_fact_id_3
    /witness_fact_id_4 /witness_fact_id_5
    /apply_authorization_fact /authorization_fact_shape_valid
    /authorization_fact_shape_valid_kind /authorization_issuer_allowed
    /genesis_authorization_fact /apply_authorization_fact_kind
    /capability_tag_known /empty_authorization_state;
  cbv delta;
  rewrite !inE;
  by smt().
qed.

lemma witness_fact_6_transition :
  apply_authorization_fact
    witness_authorization_state_5
    witness_authorization_state_5
    witness_alice
    witness_fact_6 =
  Some witness_authorization_state_6.
proof.
  rewrite /witness_authorization_state_5 /witness_authorization_state_6
    /witness_member_grant_alice_entry
    /witness_member_grant_bob_old_entry
    /witness_capability_grant_alice_admin_entry
    /witness_capability_grant_alice_history_entry
    /witness_capability_grant_alice_puncture_entry
    /witness_capability_grant_alice_beekem_entry
    /witness_fact_6 /witness_context_1 /witness_context_2
    /witness_context_3 /witness_context_4 /witness_context_5
    /witness_context_6
    /witness_alice /witness_bob_old
    /witness_member_tag_alice /witness_member_tag_bob_old
    /witness_fact_id_1 /witness_fact_id_2 /witness_fact_id_3
    /witness_fact_id_4 /witness_fact_id_5 /witness_fact_id_6
    /apply_authorization_fact /authorization_fact_shape_valid
    /authorization_fact_shape_valid_kind /authorization_issuer_allowed
    /genesis_authorization_fact /apply_authorization_fact_kind
    /member_tag_known /empty_authorization_state;
  cbv delta;
  rewrite !inE;
  by smt().
qed.

lemma witness_fact_7_transition :
  apply_authorization_fact
    witness_authorization_state_6
    witness_authorization_state_6
    witness_alice
    witness_fact_7 =
  Some witness_authorization_state_7.
proof.
  rewrite /witness_authorization_state_6 /witness_authorization_state_7
    /witness_member_grant_alice_entry
    /witness_member_grant_bob_old_entry
    /witness_capability_grant_alice_admin_entry
    /witness_capability_grant_alice_history_entry
    /witness_capability_grant_alice_puncture_entry
    /witness_capability_grant_alice_beekem_entry
    /witness_capability_grant_bob_old_edit_entry
    /witness_fact_7 /witness_context_1 /witness_context_2
    /witness_context_3 /witness_context_4 /witness_context_5
    /witness_context_6 /witness_context_7
    /witness_alice /witness_bob_old
    /witness_capability_tag_alice_admin
    /witness_capability_tag_alice_history
    /witness_capability_tag_alice_puncture
    /witness_capability_tag_alice_beekem
    /witness_capability_tag_bob_old_edit
    /witness_fact_id_1 /witness_fact_id_2 /witness_fact_id_3
    /witness_fact_id_4 /witness_fact_id_5 /witness_fact_id_6
    /witness_fact_id_7
    /apply_authorization_fact /authorization_fact_shape_valid
    /authorization_fact_shape_valid_kind /authorization_issuer_allowed
    /genesis_authorization_fact /apply_authorization_fact_kind
    /capability_tag_known /empty_authorization_state;
  cbv delta;
  rewrite !inE;
  by smt().
qed.
