require import AllCore List FSet.
require import ProtocolTypes CanonicalEncoding ProtocolPrimitives AuthorizationState.
require import WitnessFixtures.

(* Concrete mathematical ledger for the seven-fact honest base fixture.
   The Python reference model checks the same prefixes independently. *)

op witness_member_grant_alice_entry : member_grant_entry =
  {| mge_tag = witness_member_tag_alice;
     mge_principal = witness_alice |}.

op witness_member_grant_bob_old_entry : member_grant_entry =
  {| mge_tag = witness_member_tag_bob_old;
     mge_principal = witness_bob_old |}.

op witness_capability_grant_alice_admin_entry : capability_grant_entry =
  {| cge_tag = witness_capability_tag_alice_admin;
     cge_principal = witness_alice;
     cge_capability = CapAdmin |}.

op witness_capability_grant_alice_history_entry : capability_grant_entry =
  {| cge_tag = witness_capability_tag_alice_history;
     cge_principal = witness_alice;
     cge_capability = CapHistoryGrant |}.

op witness_capability_grant_alice_puncture_entry : capability_grant_entry =
  {| cge_tag = witness_capability_tag_alice_puncture;
     cge_principal = witness_alice;
     cge_capability = CapPuncture |}.

op witness_capability_grant_alice_beekem_entry : capability_grant_entry =
  {| cge_tag = witness_capability_tag_alice_beekem;
     cge_principal = witness_alice;
     cge_capability = CapBeeKemUpdate |}.

op witness_capability_grant_bob_old_edit_entry : capability_grant_entry =
  {| cge_tag = witness_capability_tag_bob_old_edit;
     cge_principal = witness_bob_old;
     cge_capability = CapEdit |}.

op witness_authorization_state_0 : authorization_state =
  empty_authorization_state.

op witness_authorization_state_1 : authorization_state =
  {| as_member_grants = fset1 witness_member_grant_alice_entry;
     as_removed_member_tags = fset0;
     as_capability_grants = fset0;
     as_removed_capability_tags = fset0;
     as_retired_principals = fset0;
     as_fact_ids = witness_context_1 |}.

op witness_authorization_state_2 : authorization_state =
  {| as_member_grants = fset1 witness_member_grant_alice_entry;
     as_removed_member_tags = fset0;
     as_capability_grants =
       fset1 witness_capability_grant_alice_admin_entry;
     as_removed_capability_tags = fset0;
     as_retired_principals = fset0;
     as_fact_ids = witness_context_2 |}.

op witness_authorization_state_3 : authorization_state =
  {| as_member_grants = fset1 witness_member_grant_alice_entry;
     as_removed_member_tags = fset0;
     as_capability_grants =
       fset1 witness_capability_grant_alice_admin_entry `|`
       fset1 witness_capability_grant_alice_history_entry;
     as_removed_capability_tags = fset0;
     as_retired_principals = fset0;
     as_fact_ids = witness_context_3 |}.

op witness_authorization_state_4 : authorization_state =
  {| as_member_grants = fset1 witness_member_grant_alice_entry;
     as_removed_member_tags = fset0;
     as_capability_grants =
       (fset1 witness_capability_grant_alice_admin_entry `|`
        fset1 witness_capability_grant_alice_history_entry) `|`
       fset1 witness_capability_grant_alice_puncture_entry;
     as_removed_capability_tags = fset0;
     as_retired_principals = fset0;
     as_fact_ids = witness_context_4 |}.

op witness_authorization_state_5 : authorization_state =
  {| as_member_grants = fset1 witness_member_grant_alice_entry;
     as_removed_member_tags = fset0;
     as_capability_grants =
       ((fset1 witness_capability_grant_alice_admin_entry `|`
         fset1 witness_capability_grant_alice_history_entry) `|`
        fset1 witness_capability_grant_alice_puncture_entry) `|`
       fset1 witness_capability_grant_alice_beekem_entry;
     as_removed_capability_tags = fset0;
     as_retired_principals = fset0;
     as_fact_ids = witness_context_5 |}.

op witness_authorization_state_6 : authorization_state =
  {| as_member_grants =
       fset1 witness_member_grant_alice_entry `|`
       fset1 witness_member_grant_bob_old_entry;
     as_removed_member_tags = fset0;
     as_capability_grants =
       ((fset1 witness_capability_grant_alice_admin_entry `|`
         fset1 witness_capability_grant_alice_history_entry) `|`
        fset1 witness_capability_grant_alice_puncture_entry) `|`
       fset1 witness_capability_grant_alice_beekem_entry;
     as_removed_capability_tags = fset0;
     as_retired_principals = fset0;
     as_fact_ids = witness_context_6 |}.

op witness_authorization_state_7 : authorization_state =
  {| as_member_grants =
       fset1 witness_member_grant_alice_entry `|`
       fset1 witness_member_grant_bob_old_entry;
     as_removed_member_tags = fset0;
     as_capability_grants =
       (((fset1 witness_capability_grant_alice_admin_entry `|`
          fset1 witness_capability_grant_alice_history_entry) `|`
         fset1 witness_capability_grant_alice_puncture_entry) `|`
        fset1 witness_capability_grant_alice_beekem_entry) `|`
       fset1 witness_capability_grant_bob_old_edit_entry;
     as_removed_capability_tags = fset0;
     as_retired_principals = fset0;
     as_fact_ids = witness_context_7 |}.

op witness_signed_fact_of (fact : authorization_fact) :
    signed_authorization_fact =
  {| saf_fact = fact;
     saf_signature =
       {| sig_verification_key = fact.`af_issuer.`p_verification_key;
          sig_bytes = SignatureBytes (fact_signature_message fact) |} |}.

op witness_signed_fact_1 : signed_authorization_fact =
  witness_signed_fact_of witness_fact_1.
op witness_signed_fact_2 : signed_authorization_fact =
  witness_signed_fact_of witness_fact_2.
op witness_signed_fact_3 : signed_authorization_fact =
  witness_signed_fact_of witness_fact_3.
op witness_signed_fact_4 : signed_authorization_fact =
  witness_signed_fact_of witness_fact_4.
op witness_signed_fact_5 : signed_authorization_fact =
  witness_signed_fact_of witness_fact_5.
op witness_signed_fact_6 : signed_authorization_fact =
  witness_signed_fact_of witness_fact_6.
op witness_signed_fact_7 : signed_authorization_fact =
  witness_signed_fact_of witness_fact_7.

op witness_base_signed_facts : signed_authorization_fact list =
  [witness_signed_fact_1;
   witness_signed_fact_2;
   witness_signed_fact_3;
   witness_signed_fact_4;
   witness_signed_fact_5;
   witness_signed_fact_6;
   witness_signed_fact_7].

lemma witness_fact_id_2_neq_1 :
  witness_fact_id_2 <> witness_fact_id_1.
proof.
  by rewrite /witness_fact_id_2 /witness_fact_id_1; smt().
qed.

lemma witness_fact_id_3_neq_1 :
  witness_fact_id_3 <> witness_fact_id_1.
proof.
  by rewrite /witness_fact_id_3 /witness_fact_id_1; smt().
qed.

lemma witness_fact_id_3_neq_2 :
  witness_fact_id_3 <> witness_fact_id_2.
proof.
  by rewrite /witness_fact_id_3 /witness_fact_id_2; smt().
qed.

lemma no_member_grant_in_empty_trace (tag : member_tag) :
  ! (exists (entry : member_grant_entry),
       entry \in fset0<:member_grant_entry> /\
       entry.`mge_tag = tag).
proof.
  smt(in_fset0).
qed.

lemma no_capability_grant_in_empty_trace (tag : capability_tag) :
  ! (exists (entry : capability_grant_entry),
       entry \in fset0<:capability_grant_entry> /\
       entry.`cge_tag = tag).
proof.
  smt(in_fset0).
qed.

lemma witness_fact_1_transition :
  apply_authorization_fact
    witness_authorization_state_0
    witness_authorization_state_0
    witness_alice
    witness_fact_1 =
  Some witness_authorization_state_1.
proof.
  rewrite /witness_authorization_state_0 /witness_authorization_state_1
    /witness_member_grant_alice_entry
    /witness_fact_1 /witness_context_0 /witness_context_1
    /witness_alice /witness_member_tag_alice /witness_fact_id_1
    /apply_authorization_fact /authorization_fact_shape_valid
    /authorization_fact_shape_valid_kind /authorization_issuer_allowed
    /genesis_authorization_fact /apply_authorization_fact_kind
    /member_tag_known /empty_authorization_state;
  cbv delta;
  by rewrite !inE no_member_grant_in_empty_trace !fset0U.
qed.

lemma witness_fact_2_transition :
  apply_authorization_fact
    witness_authorization_state_1
    witness_authorization_state_1
    witness_alice
    witness_fact_2 =
  Some witness_authorization_state_2.
proof.
  rewrite /witness_authorization_state_1 /witness_authorization_state_2
    /witness_member_grant_alice_entry
    /witness_capability_grant_alice_admin_entry
    /witness_fact_2 /witness_context_1 /witness_context_2
    /witness_alice /witness_capability_tag_alice_admin
    /witness_fact_id_1 /witness_fact_id_2
    /apply_authorization_fact /authorization_fact_shape_valid
    /authorization_fact_shape_valid_kind /authorization_issuer_allowed
    /genesis_authorization_fact /apply_authorization_fact_kind
    /capability_tag_known /empty_authorization_state;
  cbv delta;
  rewrite !inE witness_fact_id_2_neq_1
    no_capability_grant_in_empty_trace !fset0U;
  by smt().
qed.

lemma witness_fact_3_shape_valid :
  authorization_fact_shape_valid witness_fact_3.
proof.
  by rewrite /authorization_fact_shape_valid
    /authorization_fact_shape_valid_kind /witness_fact_3.
qed.

lemma witness_fact_3_id_fresh :
  witness_fact_3.`af_id \notin witness_authorization_state_2.`as_fact_ids.
proof.
  rewrite /witness_fact_3 /witness_authorization_state_2
    /witness_context_2 /witness_context_1.
  smt(in_fsetU in_fset1
    witness_fact_id_3_neq_1 witness_fact_id_3_neq_2).
qed.

lemma witness_alice_active_state_2 :
  member_active Production witness_authorization_state_2 witness_alice.
proof.
  rewrite /member_active /witness_authorization_state_2
    /witness_member_grant_alice_entry /principal_matches /defense_enabled.
  smt(in_fset1 in_fset0).
qed.

lemma witness_fact_3_issuer_allowed :
  authorization_issuer_allowed
    witness_authorization_state_2
    witness_authorization_state_2
    witness_alice
    witness_fact_3.
proof.
  by rewrite /authorization_issuer_allowed /genesis_authorization_fact
    /witness_fact_3 witness_alice_active_state_2.
qed.

lemma witness_fact_3_kind_application :
  apply_authorization_fact_kind
    witness_fact_3.`af_kind
    witness_authorization_state_2
    witness_fact_3 =
  Some witness_authorization_state_3.
proof.
  rewrite /apply_authorization_fact_kind /witness_fact_3
    /witness_authorization_state_2 /witness_authorization_state_3
    /witness_capability_grant_alice_admin_entry
    /witness_capability_grant_alice_history_entry
    /witness_capability_tag_alice_admin
    /witness_capability_tag_alice_history
    /witness_context_3 /capability_tag_known.
  by rewrite !inE; smt().
qed.

lemma witness_fact_3_transition :
  apply_authorization_fact
    witness_authorization_state_2
    witness_authorization_state_2
    witness_alice
    witness_fact_3 =
  Some witness_authorization_state_3.
proof.
  rewrite /apply_authorization_fact witness_fact_3_shape_valid
    witness_fact_3_id_fresh witness_fact_3_issuer_allowed.
  exact witness_fact_3_kind_application.
qed.
