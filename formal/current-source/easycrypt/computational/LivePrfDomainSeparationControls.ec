require import AllCore List FSet Distr.
require import ProtocolTypes ProtocolChecks CanonicalEncoding ProtocolPrimitives.
require import AuthorizationState AuthorizationAncestry.
require import LiveKeyGame LiveKeyWitnesses.
require import LivePrfTypes LivePrfGame LivePrfApplicationReduction.

(* Deliberate one-line KDF mutation: the ordinary history domain reuses the
   live-domain material formula.  The procedure signatures and typed oracle
   transcript remain unchanged; only the live/history separation in the KDF is
   removed.  This is a counterexample control, never a production schedule. *)
op collapsed_history_material
    (secret : beekem_secret)
    (label : history_key_label) : int =
  with secret = BeeKemSecret value =>
    value + label.`hkl_protocol_version.

op live_application_key_material
    (key : live_application_key) : int =
  with key = LiveApplicationKey material label => material.

op history_domain_output_material
    (output : history_domain_output) : int =
  with output = HistoryDomainOutput material label => material.

op live_history_materials_equal
    (live_key : live_application_key)
    (history_output : history_domain_output) : bool =
  live_application_key_material live_key =
  history_domain_output_material history_output.

module CollapsedLiveHistoryKeySchedule : MULTI_DOMAIN_KEY_SCHEDULE = {
  proc derive_live(
    secret : beekem_secret,
    label : live_key_label
  ) : live_application_key = {
    return LiveApplicationKey (test_live_material secret label) label;
  }

  proc derive_history(
    secret : beekem_secret,
    label : history_key_label
  ) : history_domain_output = {
    return HistoryDomainOutput (collapsed_history_material secret label) label;
  }

  proc derive_history_capability(
    secret : beekem_secret,
    label : history_key_label,
    cover : segment_cover
  ) : history_capability_output = {
    return
      HistoryCapabilityOutput
        (test_history_material secret label) label cover;
  }
}.

(* The application obtains a permitted history-domain disclosure at the same
   installed BeeKEM node that it then challenges in the live domain.  It never
   calls a primitive oracle directly. *)
module CollapsedLiveHistoryApplicationAdversary(
  O : LIVE_PROTOCOL_ORACLE
) = {
  var history_answer : history_domain_output option
  var challenge_answer : live_application_key option

  proc attack() : unit = {
    var created : node_id option;
    var updated : node_id option;

    history_answer <- None;
    challenge_answer <- None;

    created <@ O.create_group(live_witness_creator, fset0);
    updated <@ O.send_beekem_update(live_witness_creator);
    history_answer <@ O.reveal_history_output(
      live_witness_creator, NodeId 2, SegmentId 908
    );
    challenge_answer <@ O.challenge_live(
      live_witness_creator, NodeId 2
    );
  }

  proc guess() : bool = {
    var result : bool;

    result <- false;
    if (history_answer <> None /\ challenge_answer <> None) {
      result <-
        live_history_materials_equal
          (oget challenge_answer) (oget history_answer);
    }
    return result;
  }
}.

module CollapsedLiveHistoryApplicationGame = MultiDomainPrfGame(
  BPRFLive(
    CollapsedLiveHistoryApplicationAdversary,
    TestSignature,
    TestNodeHash,
    TestBeeKemLiveRuntime
  ),
  CollapsedLiveHistoryKeySchedule,
  TestLiveKeySampler
).

lemma collapsed_live_history_application_fixed_real :
  hoare [CollapsedLiveHistoryApplicationGame.main_with_fixed_bit :
       arg.`4 = true
    ==>
       res.`mpge_win
    /\ res.`mpge_eligible
    /\ res.`mpge_guess
    /\ res.`mpge_live_query_count = 0
    /\ res.`mpge_live_challenge_count = 1
    /\ res.`mpge_history_query_count = 1
    /\ res.`mpge_history_capability_query_count = 0].
proof.
  proc.
  inline *.
  auto.
  rewrite /live_witness_protocol_state /live_witness_creator
    /live_initial_authorization /live_initial_authorization_digest
    /authorization_policy_replay /authorization_policy_replay_from
    /empty_active_member_store /active_member_store_put
    /active_member_store_of_set
    /empty_control_store /empty_node_digest_store
    /empty_delivery_store /empty_member_secret_store
    /empty_member_head_store /empty_causal_relation
    /control_store_put /node_digest_store_put
    /delivery_store_put /member_secret_store_put
    /member_head_store_put /node_after /test_secret_for_node
    /history_label_of /live_label_of
    /test_live_material /test_history_material
    /collapsed_history_material /live_history_materials_equal
    /live_application_key_material /history_domain_output_material
    /all_nodes_known /all_nodes_known_list
    /all_predecessors_delivered /all_predecessors_delivered_list
    /causal_relation_extend /predecessor_reaches_list
    /challenge_query_count /query_is_challenge
    /live_trace_admissible /bee_safe_kappa
    /every_challenge_safe /query_challenge_member
    /every_compromise_safe_for_challenge /query_compromise_member
    /mdprf_live_query_count /mdprf_live_challenge_count
    /mdprf_history_query_count
    /mdprf_history_capability_query_count
    /mdprf_query_is_live_query /mdprf_query_is_live_challenge
    /mdprf_query_is_history /mdprf_query_is_history_capability
    /mdprf_kind_is_live_query /mdprf_kind_is_live_challenge
    /mdprf_kind_is_history /mdprf_kind_is_history_capability /=.
  by rewrite !inE; smt().
qed.

lemma collapsed_live_history_application_fixed_random :
  hoare [CollapsedLiveHistoryApplicationGame.main_with_fixed_bit :
       arg.`4 = false
    ==>
       res.`mpge_win
    /\ res.`mpge_eligible
    /\ ! res.`mpge_guess
    /\ res.`mpge_live_query_count = 0
    /\ res.`mpge_live_challenge_count = 1
    /\ res.`mpge_history_query_count = 1
    /\ res.`mpge_history_capability_query_count = 0].
proof.
  proc.
  inline *.
  auto.
  rewrite /live_witness_protocol_state /live_witness_creator
    /live_initial_authorization /live_initial_authorization_digest
    /authorization_policy_replay /authorization_policy_replay_from
    /empty_active_member_store /active_member_store_put
    /active_member_store_of_set
    /empty_control_store /empty_node_digest_store
    /empty_delivery_store /empty_member_secret_store
    /empty_member_head_store /empty_causal_relation
    /control_store_put /node_digest_store_put
    /delivery_store_put /member_secret_store_put
    /member_head_store_put /node_after /test_secret_for_node
    /history_label_of /live_label_of
    /test_live_material /test_history_material
    /collapsed_history_material /live_history_materials_equal
    /live_application_key_material /history_domain_output_material
    /all_nodes_known /all_nodes_known_list
    /all_predecessors_delivered /all_predecessors_delivered_list
    /causal_relation_extend /predecessor_reaches_list
    /challenge_query_count /query_is_challenge
    /live_trace_admissible /bee_safe_kappa
    /every_challenge_safe /query_challenge_member
    /every_compromise_safe_for_challenge /query_compromise_member
    /mdprf_live_query_count /mdprf_live_challenge_count
    /mdprf_history_query_count
    /mdprf_history_capability_query_count
    /mdprf_query_is_live_query /mdprf_query_is_live_challenge
    /mdprf_query_is_history /mdprf_query_is_history_capability
    /mdprf_kind_is_live_query /mdprf_kind_is_live_challenge
    /mdprf_kind_is_history /mdprf_kind_is_history_capability /=.
  by rewrite !inE; smt().
qed.

lemma collapsed_live_history_application_game_probability_one
    &m
    (initial_state : protocol_state)
    (initial_facts : signed_authorization_fact list)
    (retention_kappa : int) :
  Pr[
    CollapsedLiveHistoryApplicationGame.main(
      initial_state, initial_facts, retention_kappa
    ) @ &m : res
  ] = 1%r.
proof.
  byphoare => //.
  proc.
  inline CollapsedLiveHistoryApplicationGame.main_with_evidence.
  seq 1 : true 1%r 1%r 0%r 0%r.
  + rnd.
  + case (hidden_bit).
    + call collapsed_live_history_application_fixed_real.
      auto.
    + call collapsed_live_history_application_fixed_random.
      auto.
qed.

lemma collapsed_live_history_application_normalized_advantage_half
    &m
    (initial_state : protocol_state)
    (initial_facts : signed_authorization_fact list)
    (retention_kappa : int) :
  mdprf_normalized_advantage
    (Pr[
       CollapsedLiveHistoryApplicationGame.main(
         initial_state, initial_facts, retention_kappa
       ) @ &m : res
     ])
    1%r = 1%r / 2%r.
proof.
  rewrite collapsed_live_history_application_game_probability_one.
  rewrite /mdprf_normalized_advantage.
  by smt().
qed.
