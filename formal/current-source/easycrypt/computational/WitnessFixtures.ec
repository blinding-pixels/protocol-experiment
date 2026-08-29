require import AllCore List FSet.
require import ProtocolTypes CanonicalEncoding ProtocolPrimitives AuthorizationState.
require import ProtocolChecks ProtocolOracles UnauthorizedGame.

op witness_alice : principal =
  {| p_verification_key = VerificationKey 1;
     p_incarnation_nonce = IncarnationNonce 1 |}.

op witness_bob_old : principal =
  {| p_verification_key = VerificationKey 2;
     p_incarnation_nonce = IncarnationNonce 1 |}.

op witness_bob_new : principal =
  {| p_verification_key = VerificationKey 2;
     p_incarnation_nonce = IncarnationNonce 2 |}.

op witness_carol : principal =
  {| p_verification_key = VerificationKey 3;
     p_incarnation_nonce = IncarnationNonce 1 |}.

op witness_document : document_id = DocumentId 1.
op witness_other_document : document_id = DocumentId 2.
op witness_base_node : node_id = NodeId 1.
op witness_extended_node : node_id = NodeId 2.
op witness_rejoin_node : node_id = NodeId 3.
op witness_missing_revoke_node : node_id = NodeId 4.
op witness_beekem_path : beekem_path = BeeKemPath 1.
op witness_merge_node : merge_node = MergeNode 1.
op witness_other_merge_node : merge_node = MergeNode 2.
op witness_segment : segment_id = SegmentId 1.
op witness_other_segment : segment_id = SegmentId 2.
op witness_path : path_bits = PathBits 0.
op witness_other_path : path_bits = PathBits 1.

op witness_region_interval : region_interval =
  {| ri_segment = witness_segment; ri_start = 0; ri_end = 4 |}.

op witness_enlarged_region_interval : region_interval =
  {| ri_segment = witness_segment; ri_start = 0; ri_end = 8 |}.

op witness_region : region = fset1 witness_region_interval.
op witness_enlarged_region : region = fset1 witness_enlarged_region_interval.

op witness_cover_entry : subtree_cover_entry =
  {| sce_segment = witness_segment;
     sce_path = witness_path;
     sce_depth = 1 |}.

op witness_other_cover_entry : subtree_cover_entry =
  {| sce_segment = witness_segment;
     sce_path = witness_other_path;
     sce_depth = 1 |}.

op witness_cross_segment_cover_entry : subtree_cover_entry =
  {| sce_segment = witness_other_segment;
     sce_path = witness_path;
     sce_depth = 1 |}.

op witness_cover : segment_cover = fset1 witness_cover_entry.
op witness_other_cover : segment_cover = fset1 witness_other_cover_entry.
op witness_cross_segment_cover : segment_cover =
  fset1 witness_cross_segment_cover_entry.

op witness_member_tag_alice : member_tag = MemberTag 1.
op witness_member_tag_bob_old : member_tag = MemberTag 2.
op witness_member_tag_bob_new : member_tag = MemberTag 3.
op witness_member_tag_carol : member_tag = MemberTag 4.

op witness_capability_tag_alice_admin : capability_tag = CapabilityTag 1.
op witness_capability_tag_alice_history : capability_tag = CapabilityTag 2.
op witness_capability_tag_alice_puncture : capability_tag = CapabilityTag 3.
op witness_capability_tag_alice_beekem : capability_tag = CapabilityTag 4.
op witness_capability_tag_bob_old_edit : capability_tag = CapabilityTag 5.
op witness_capability_tag_bob_new_edit : capability_tag = CapabilityTag 6.

op witness_fact_id_1 : fact_id = FactId 1.
op witness_fact_id_2 : fact_id = FactId 2.
op witness_fact_id_3 : fact_id = FactId 3.
op witness_fact_id_4 : fact_id = FactId 4.
op witness_fact_id_5 : fact_id = FactId 5.
op witness_fact_id_6 : fact_id = FactId 6.
op witness_fact_id_7 : fact_id = FactId 7.
op witness_fact_id_8 : fact_id = FactId 8.
op witness_fact_id_9 : fact_id = FactId 9.
op witness_fact_id_10 : fact_id = FactId 10.

op witness_context_0 : fact_id fset = fset0.
op witness_context_1 : fact_id fset = fset1 witness_fact_id_1.
op witness_context_2 : fact_id fset =
  witness_context_1 `|` fset1 witness_fact_id_2.
op witness_context_3 : fact_id fset =
  witness_context_2 `|` fset1 witness_fact_id_3.
op witness_context_4 : fact_id fset =
  witness_context_3 `|` fset1 witness_fact_id_4.
op witness_context_5 : fact_id fset =
  witness_context_4 `|` fset1 witness_fact_id_5.
op witness_context_6 : fact_id fset =
  witness_context_5 `|` fset1 witness_fact_id_6.
op witness_context_7 : fact_id fset =
  witness_context_6 `|` fset1 witness_fact_id_7.
op witness_context_8 : fact_id fset =
  witness_context_7 `|` fset1 witness_fact_id_8.
op witness_context_9 : fact_id fset =
  witness_context_8 `|` fset1 witness_fact_id_9.
op witness_context_10 : fact_id fset =
  witness_context_9 `|` fset1 witness_fact_id_10.

op witness_fact_1 : authorization_fact =
  {| af_id = witness_fact_id_1;
     af_kind = GenesisMembership;
     af_issuer = witness_alice;
     af_context = witness_context_0;
     af_target = Some witness_alice;
     af_capability = None;
     af_member_tag = Some witness_member_tag_alice;
     af_capability_tag = None;
     af_observed_member_tags = fset0;
     af_observed_capability_tags = fset0 |}.

op witness_fact_2 : authorization_fact =
  {| af_id = witness_fact_id_2;
     af_kind = GenesisCapability;
     af_issuer = witness_alice;
     af_context = witness_context_1;
     af_target = Some witness_alice;
     af_capability = Some CapAdmin;
     af_member_tag = None;
     af_capability_tag = Some witness_capability_tag_alice_admin;
     af_observed_member_tags = fset0;
     af_observed_capability_tags = fset0 |}.

op witness_fact_3 : authorization_fact =
  {| af_id = witness_fact_id_3;
     af_kind = GenesisCapability;
     af_issuer = witness_alice;
     af_context = witness_context_2;
     af_target = Some witness_alice;
     af_capability = Some CapHistoryGrant;
     af_member_tag = None;
     af_capability_tag = Some witness_capability_tag_alice_history;
     af_observed_member_tags = fset0;
     af_observed_capability_tags = fset0 |}.

op witness_fact_4 : authorization_fact =
  {| af_id = witness_fact_id_4;
     af_kind = GenesisCapability;
     af_issuer = witness_alice;
     af_context = witness_context_3;
     af_target = Some witness_alice;
     af_capability = Some CapPuncture;
     af_member_tag = None;
     af_capability_tag = Some witness_capability_tag_alice_puncture;
     af_observed_member_tags = fset0;
     af_observed_capability_tags = fset0 |}.

op witness_fact_5 : authorization_fact =
  {| af_id = witness_fact_id_5;
     af_kind = GenesisCapability;
     af_issuer = witness_alice;
     af_context = witness_context_4;
     af_target = Some witness_alice;
     af_capability = Some CapBeeKemUpdate;
     af_member_tag = None;
     af_capability_tag = Some witness_capability_tag_alice_beekem;
     af_observed_member_tags = fset0;
     af_observed_capability_tags = fset0 |}.

op witness_fact_6 : authorization_fact =
  {| af_id = witness_fact_id_6;
     af_kind = GenesisMembership;
     af_issuer = witness_alice;
     af_context = witness_context_5;
     af_target = Some witness_bob_old;
     af_capability = None;
     af_member_tag = Some witness_member_tag_bob_old;
     af_capability_tag = None;
     af_observed_member_tags = fset0;
     af_observed_capability_tags = fset0 |}.

op witness_fact_7 : authorization_fact =
  {| af_id = witness_fact_id_7;
     af_kind = GenesisCapability;
     af_issuer = witness_alice;
     af_context = witness_context_6;
     af_target = Some witness_bob_old;
     af_capability = Some CapEdit;
     af_member_tag = None;
     af_capability_tag = Some witness_capability_tag_bob_old_edit;
     af_observed_member_tags = fset0;
     af_observed_capability_tags = fset0 |}.

op witness_carol_grant_fact : authorization_fact =
  {| af_id = witness_fact_id_8;
     af_kind = MembershipGrant;
     af_issuer = witness_alice;
     af_context = witness_context_7;
     af_target = Some witness_carol;
     af_capability = None;
     af_member_tag = Some witness_member_tag_carol;
     af_capability_tag = None;
     af_observed_member_tags = fset0;
     af_observed_capability_tags = fset0 |}.

op witness_bob_revoke_fact : authorization_fact =
  {| af_id = witness_fact_id_8;
     af_kind = MembershipRevoke;
     af_issuer = witness_alice;
     af_context = witness_context_7;
     af_target = None;
     af_capability = None;
     af_member_tag = None;
     af_capability_tag = None;
     af_observed_member_tags = fset1 witness_member_tag_bob_old;
     af_observed_capability_tags = fset0 |}.

op witness_bob_new_membership_fact : authorization_fact =
  {| af_id = witness_fact_id_9;
     af_kind = MembershipGrant;
     af_issuer = witness_alice;
     af_context = witness_context_8;
     af_target = Some witness_bob_new;
     af_capability = None;
     af_member_tag = Some witness_member_tag_bob_new;
     af_capability_tag = None;
     af_observed_member_tags = fset0;
     af_observed_capability_tags = fset0 |}.

op witness_bob_new_edit_fact : authorization_fact =
  {| af_id = witness_fact_id_10;
     af_kind = CapabilityGrant;
     af_issuer = witness_alice;
     af_context = witness_context_9;
     af_target = Some witness_bob_new;
     af_capability = Some CapEdit;
     af_member_tag = None;
     af_capability_tag = Some witness_capability_tag_bob_new_edit;
     af_observed_member_tags = fset0;
     af_observed_capability_tags = fset0 |}.

op witness_missing_capability_revoke_fact : authorization_fact =
  {| af_id = witness_fact_id_8;
     af_kind = CapabilityRevoke;
     af_issuer = witness_alice;
     af_context = witness_context_7;
     af_target = None;
     af_capability = None;
     af_member_tag = None;
     af_capability_tag = None;
     af_observed_member_tags = fset0;
     af_observed_capability_tags =
       fset1 witness_capability_tag_bob_old_edit |}.

op witness_history_expectation : history_expectation =
  {| he_issuer = witness_alice;
     he_recipient = witness_bob_old;
     he_merge_node = witness_merge_node;
     he_region = witness_region;
     he_cover = witness_cover |}.

(* Exact immutable fact contents named by each fixture's causal closure.  The
   alternatives sharing fact id 8 deliberately live in different fixture
   states; a view cannot substitute one for another inside a fixed state. *)
op witness_base_authorization_facts : authorization_fact list =
  [witness_fact_1; witness_fact_2; witness_fact_3; witness_fact_4;
   witness_fact_5; witness_fact_6; witness_fact_7].

op witness_extended_authorization_facts : authorization_fact list =
  rcons witness_base_authorization_facts witness_carol_grant_fact.

op witness_rejoin_authorization_facts : authorization_fact list =
  rcons
    (rcons
      (rcons witness_base_authorization_facts witness_bob_revoke_fact)
      witness_bob_new_membership_fact)
    witness_bob_new_edit_fact.

op witness_missing_revoke_authorization_facts : authorization_fact list =
  rcons witness_base_authorization_facts
    witness_missing_capability_revoke_fact.

op witness_fact_contents_for_node (node : node_id) : fact_content_map =
  if node = witness_extended_node
  then fact_content_map_of_authorization_facts
         witness_extended_authorization_facts
  else if node = witness_rejoin_node
  then fact_content_map_of_authorization_facts
         witness_rejoin_authorization_facts
  else if node = witness_missing_revoke_node
  then fact_content_map_of_authorization_facts
         witness_missing_revoke_authorization_facts
  else fact_content_map_of_authorization_facts
         witness_base_authorization_facts.

op witness_closure_map
    (node : node_id)
    (context : fact_id fset) : closure_map =
  fun candidate => if candidate = node then Some context else None.

op witness_beekem_path_map
    (predecessors : node_id fset)
    (path : beekem_path) : beekem_path_map =
  fun candidate => if candidate = predecessors then Some path else None.

op witness_protocol_state
    (node : node_id)
    (context : fact_id fset) : protocol_state =
  {| ps_creator = witness_alice;
     ps_document_id = witness_document;
     ps_nodes = fset1 node;
     ps_closures = witness_closure_map node context;
     ps_fact_contents = witness_fact_contents_for_node node;
     ps_seen_operation_ids = fset0;
     ps_seen_nonces = fset0;
     ps_beekem_paths =
       witness_beekem_path_map (fset1 node) witness_beekem_path;
     ps_history_expectation = Some witness_history_expectation;
     ps_expected_puncture_regions = fset1 witness_region |}.

type witness_fixture = {
  wf_state : protocol_state;
  wf_facts : signed_authorization_fact list;
  wf_authorization_valid : bool;
  wf_authorization : authorization_state
}.

module WitnessFixtures = {
  proc sign_fact(fact : authorization_fact) : signed_authorization_fact = {
    var sig : signature;
    sig <@ TestSignature.sign(
      fact.`af_issuer.`p_verification_key,
      fact_signature_message fact
    );
    return {| saf_fact = fact; saf_signature = sig |};
  }

  proc sign_operation(
    mode : validator_mode,
    envelope : operation_envelope,
    signing_key : verification_key
  ) : signed_operation = {
    var sig : signature;
    sig <@ TestSignature.sign(
      signing_key,
      operation_signature_message mode envelope
    );
    return {| so_raw = encode_operation envelope; so_signature = sig |};
  }

  proc base() : witness_fixture = {
    var s1 : signed_authorization_fact;
    var s2 : signed_authorization_fact;
    var s3 : signed_authorization_fact;
    var s4 : signed_authorization_fact;
    var s5 : signed_authorization_fact;
    var s6 : signed_authorization_fact;
    var s7 : signed_authorization_fact;
    var facts : signed_authorization_fact list;
    var valid : bool;
    var authorization : authorization_state;

    s1 <@ sign_fact(witness_fact_1);
    s2 <@ sign_fact(witness_fact_2);
    s3 <@ sign_fact(witness_fact_3);
    s4 <@ sign_fact(witness_fact_4);
    s5 <@ sign_fact(witness_fact_5);
    s6 <@ sign_fact(witness_fact_6);
    s7 <@ sign_fact(witness_fact_7);
    facts <- [s1; s2; s3; s4; s5; s6; s7];
    (valid, authorization) <@
      NormalizeAuthorization(TestSignature).normalize(facts, witness_alice);

    return
      {| wf_state =
           witness_protocol_state witness_base_node witness_context_7;
         wf_facts = facts;
         wf_authorization_valid = valid;
         wf_authorization = authorization |};
  }

  proc extended() : witness_fixture = {
    var base_fixture : witness_fixture;
    var s8 : signed_authorization_fact;
    var facts : signed_authorization_fact list;
    var valid : bool;
    var authorization : authorization_state;

    base_fixture <@ base();
    s8 <@ sign_fact(witness_carol_grant_fact);
    facts <- rcons base_fixture.`wf_facts s8;
    (valid, authorization) <@
      NormalizeAuthorization(TestSignature).normalize(facts, witness_alice);

    return
      {| wf_state =
           witness_protocol_state witness_extended_node witness_context_8;
         wf_facts = facts;
         wf_authorization_valid = valid;
         wf_authorization = authorization |};
  }

  proc rejoin() : witness_fixture = {
    var base_fixture : witness_fixture;
    var s8 : signed_authorization_fact;
    var s9 : signed_authorization_fact;
    var s10 : signed_authorization_fact;
    var facts : signed_authorization_fact list;
    var valid : bool;
    var authorization : authorization_state;

    base_fixture <@ base();
    s8 <@ sign_fact(witness_bob_revoke_fact);
    s9 <@ sign_fact(witness_bob_new_membership_fact);
    s10 <@ sign_fact(witness_bob_new_edit_fact);
    facts <- rcons (rcons (rcons base_fixture.`wf_facts s8) s9) s10;
    (valid, authorization) <@
      NormalizeAuthorization(TestSignature).normalize(facts, witness_alice);

    return
      {| wf_state =
           witness_protocol_state witness_rejoin_node witness_context_10;
         wf_facts = facts;
         wf_authorization_valid = valid;
         wf_authorization = authorization |};
  }

  proc missing_revocation() : witness_fixture = {
    var base_fixture : witness_fixture;
    base_fixture <@ base();
    return
      {| wf_state =
           witness_protocol_state
             witness_missing_revoke_node witness_context_8;
         wf_facts = base_fixture.`wf_facts;
         wf_authorization_valid = base_fixture.`wf_authorization_valid;
         wf_authorization = base_fixture.`wf_authorization |};
  }
}.

op witness_edit_envelope(
    domain : protocol_domain,
    version : int,
    document : document_id,
    oid : operation_id,
    author : principal,
    required : capability,
    predecessors : node_id fset,
    digest : authorization_digest,
    body : operation_body,
    operation_nonce : nonce
) : operation_envelope =
  {| oe_protocol_domain = domain;
     oe_protocol_version = version;
     oe_document_id = document;
     oe_operation_id = oid;
     oe_author = author;
     oe_required_capability = required;
     oe_direct_predecessors = predecessors;
     oe_authorization_digest = digest;
     oe_operation_kind = OpEdit;
     oe_operation_body = body;
     oe_nonce = operation_nonce |}.

op witness_history_envelope(
    oid : operation_id,
    digest : authorization_digest,
    recipient : principal,
    merge : merge_node,
    selected : region,
    cover : segment_cover,
    operation_nonce : nonce
) : operation_envelope =
  {| oe_protocol_domain = ProtocolDomain 1;
     oe_protocol_version = 1;
     oe_document_id = witness_document;
     oe_operation_id = oid;
     oe_author = witness_alice;
     oe_required_capability = CapHistoryGrant;
     oe_direct_predecessors = fset1 witness_base_node;
     oe_authorization_digest = digest;
     oe_operation_kind = OpHistoryGrant;
     oe_operation_body =
       HistoryGrantBody recipient merge selected cover;
     oe_nonce = operation_nonce |}.

op witness_public_view(
    facts : signed_authorization_fact list,
    observed : fact_id fset
) : public_view =
  {| pv_facts = facts; pv_observed_fact_ids = observed |}.
