require import AllCore List FSet.
require import ProtocolTypes CanonicalEncoding ProtocolPrimitives AuthorizationState.
require import ProtocolChecks PrimitiveGames UnauthorizedOriginGame LiveKeyGame.

import PG.

op live_witness_creator : principal =
  {| p_verification_key = VerificationKey 700;
     p_incarnation_nonce = IncarnationNonce 701 |}.

op live_witness_document : document_id = DocumentId 702.

op live_witness_protocol_state : protocol_state =
  {| ps_creator = live_witness_creator;
     ps_document_id = live_witness_document;
     ps_nodes = fset0;
     ps_closures = fun _ => None;
     ps_fact_contents = fun _ => None;
     ps_seen_operation_ids = fset0;
     ps_seen_nonces = fset0;
     ps_beekem_paths = fun _ => None;
     ps_history_expectation = None;
     ps_expected_puncture_regions = fset0 |}.

op live_witness_challenge_query : live_query =
  {| lq_kind = LiveChallengeQuery live_witness_creator;
     lq_operation = Some (NodeId 2) |}.

op live_witness_compromise_same_node_query : live_query =
  {| lq_kind = LiveCompromiseQuery live_witness_creator;
     lq_operation = Some (NodeId 2) |}.

lemma single_challenge_without_compromise_is_bee_safe
    (retention_kappa : int)
    (relation : causal_relation) :
  1 <= retention_kappa =>
  bee_safe_kappa
    retention_kappa relation [live_witness_challenge_query].
proof.
  move=> kappa_positive.
  rewrite /bee_safe_kappa /every_challenge_safe
    /query_challenge_member
    /every_compromise_safe_for_challenge /=.
  by smt().
qed.

lemma immediate_same_node_compromise_is_not_bee_safe
    (retention_kappa : int) :
  1 <= retention_kappa =>
  ! bee_safe_kappa
      retention_kappa
      empty_causal_relation
      [live_witness_challenge_query;
       live_witness_compromise_same_node_query].
proof.
  move=> kappa_positive.
  rewrite /bee_safe_kappa /every_challenge_safe
    /query_challenge_member
    /every_compromise_safe_for_challenge
    /query_compromise_member /bee_safe_pair
    /count_updates_between /count_updates_at_or_before
    /query_is_update_by /causally_before /causally_at_or_before
    /causally_concurrent /empty_causal_relation /=.
  by smt().
qed.

module HonestLiveTrace = {
  module SO = PG.LoggedSignatureOracle(TestSignature)
  module Auth = OriginTrackedCandidateEnvironment(SO, TestNodeHash)
  module O = LiveProtocolCore(
    Auth,
    TestBeeKemLiveRuntime,
    TestMultiDomainKeySchedule,
    TestLiveKeySampler
  )

  proc main() : bool * int * bool = {
    var created : node_id option;
    var updated : node_id option;
    var challenge : live_application_key option;

    SO.init();
    Auth.init(live_witness_protocol_state);
    O.init(
      live_witness_protocol_state,
      1,
      true,
      authorization_digest_of empty_authorization_state
    );
    created <@ O.create_group(live_witness_creator, fset0);
    updated <@ O.send_beekem_update(live_witness_creator);
    challenge <@ O.challenge_live(live_witness_creator, NodeId 2);

    return
      (challenge <> None,
       challenge_query_count O.queries,
       live_trace_admissible 1 O.relation O.queries O.runtime_fault);
  }
}.

lemma honest_live_trace_reaches_admissible_challenge :
  hoare [HonestLiveTrace.main : true ==> res = (true, 1, true)].
proof.
  proc.
  inline *.
  auto.
  rewrite /live_witness_protocol_state /live_witness_creator
    /empty_active_member_store /active_member_store_put
    /active_member_store_of_set
    /empty_control_store /empty_node_digest_store
    /empty_delivery_store /empty_member_secret_store
    /empty_member_head_store /empty_causal_relation
    /control_store_put /node_digest_store_put
    /delivery_store_put /member_secret_store_put
    /member_head_store_put /node_after /test_secret_for_node
    /live_label_of /test_live_material
    /all_nodes_known /all_nodes_known_list
    /all_predecessors_delivered /all_predecessors_delivered_list
    /causal_relation_extend /predecessor_reaches_list
    /challenge_query_count /query_is_challenge
    /live_trace_admissible /bee_safe_kappa
    /every_challenge_safe /query_challenge_member
    /every_compromise_safe_for_challenge /query_compromise_member /=.
  by rewrite !inE; smt().
qed.

module RevealThenChallengeTrace = {
  module SO = PG.LoggedSignatureOracle(TestSignature)
  module Auth = OriginTrackedCandidateEnvironment(SO, TestNodeHash)
  module O = LiveProtocolCore(
    Auth,
    TestBeeKemLiveRuntime,
    TestMultiDomainKeySchedule,
    TestLiveKeySampler
  )

  proc main() : bool = {
    var created : node_id option;
    var updated : node_id option;
    var revealed : live_application_key option;
    var challenge : live_application_key option;

    SO.init();
    Auth.init(live_witness_protocol_state);
    O.init(
      live_witness_protocol_state,
      1,
      true,
      authorization_digest_of empty_authorization_state
    );
    created <@ O.create_group(live_witness_creator, fset0);
    updated <@ O.send_beekem_update(live_witness_creator);
    revealed <@ O.reveal_live_key(live_witness_creator, NodeId 2);
    challenge <@ O.challenge_live(live_witness_creator, NodeId 2);

    return revealed <> None /\ challenge = None;
  }
}.

lemma previously_revealed_live_node_cannot_be_challenged :
  hoare [RevealThenChallengeTrace.main : true ==> res].
proof.
  proc.
  inline *.
  auto.
  rewrite /live_witness_protocol_state /live_witness_creator
    /empty_active_member_store /active_member_store_put
    /active_member_store_of_set
    /empty_control_store /empty_node_digest_store
    /empty_delivery_store /empty_member_secret_store
    /empty_member_head_store /empty_causal_relation
    /control_store_put /node_digest_store_put
    /delivery_store_put /member_secret_store_put
    /member_head_store_put /node_after /test_secret_for_node
    /live_label_of /test_live_material
    /all_nodes_known /all_nodes_known_list
    /all_predecessors_delivered /all_predecessors_delivered_list
    /causal_relation_extend /predecessor_reaches_list /=.
  by rewrite !inE; smt().
qed.
