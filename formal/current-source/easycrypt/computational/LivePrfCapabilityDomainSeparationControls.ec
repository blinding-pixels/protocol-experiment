require import AllCore List FSet Distr.
require import ProtocolTypes ProtocolChecks CanonicalEncoding ProtocolPrimitives.
require import AuthorizationState AuthorizationAncestry.
require import LiveKeyGame LiveKeyWitnesses.
require import LivePrfTypes LivePrfGame LivePrfApplicationReduction.

(* Deliberate KDF mutation for the constrained history-capability path only.
   The capability output reuses the live-domain material formula while retaining
   its typed history label and cover.  The ordinary history procedure remains
   correctly separated.  This is a counterexample control, never a production
   schedule. *)
op collapsed_capability_material
    (secret : beekem_secret)
    (label : history_key_label) : int =
  with secret = BeeKemSecret value =>
    value + label.`hkl_protocol_version.

op capability_control_live_material
    (key : live_application_key) : int =
  with key = LiveApplicationKey material label => material.

op capability_control_history_material
    (output : history_capability_output) : int =
  with output = HistoryCapabilityOutput material label cover => material.

op live_capability_materials_equal
    (live_key : live_application_key)
    (capability : history_capability_output) : bool =
  capability_control_live_material live_key =
  capability_control_history_material capability.

module CollapsedLiveCapabilityKeySchedule : MULTI_DOMAIN_KEY_SCHEDULE = {
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
    return HistoryDomainOutput (test_history_material secret label) label;
  }

  proc derive_history_capability(
    secret : beekem_secret,
    label : history_key_label,
    cover : segment_cover
  ) : history_capability_output = {
    return
      HistoryCapabilityOutput
        (collapsed_capability_material secret label) label cover;
  }
}.

(* The application obtains a permitted constrained-history disclosure for the
   same installed BeeKEM node that it then challenges in the live domain.  It
   reaches both procedures only through the application oracle. *)
module CollapsedLiveCapabilityApplicationAdversary(
  O : LIVE_PROTOCOL_ORACLE
) = {
  var capability_answer : history_capability_output option
  var challenge_answer : live_application_key option

  proc attack() : unit = {
    var created : node_id option;
    var updated : node_id option;

    capability_answer <- None;
    challenge_answer <- None;

    created <@ O.create_group(live_witness_creator, fset0);
    updated <@ O.send_beekem_update(live_witness_creator);
    capability_answer <@ O.reveal_history_capability(
      live_witness_creator, NodeId 2, SegmentId 908, fset0
    );
    challenge_answer <@ O.challenge_live(
      live_witness_creator, NodeId 2
    );
  }

  proc guess() : bool = {
    var result : bool;

    result <- false;
    if (capability_answer <> None /\ challenge_answer <> None) {
      result <-
        live_capability_materials_equal
          (oget challenge_answer) (oget capability_answer);
    }
    return result;
  }
}.

module CollapsedLiveCapabilityApplicationGame = MultiDomainPrfGame(
  BPRFLive(
    CollapsedLiveCapabilityApplicationAdversary,
    TestSignature,
    TestNodeHash,
    TestBeeKemLiveRuntime
  ),
  CollapsedLiveCapabilityKeySchedule,
  TestLiveKeySampler
).

lemma collapsed_live_capability_application_fixed_real :
  hoare [CollapsedLiveCapabilityApplicationGame.main_with_fixed_bit :
       arg.`4 = true
    ==>
       res.`mpge_win
    /\ res.`mpge_eligible
    /\ res.`mpge_guess
    /\ res.`mpge_live_query_count = 0
    /\ res.`mpge_live_challenge_count = 1
    /\ res.`mpge_history_query_count = 0
    /\ res.`mpge_history_capability_query_count = 1].
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
    /collapsed_capability_material /live_capability_materials_equal
    /capability_control_live_material /capability_control_history_material
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

lemma collapsed_live_capability_application_fixed_random :
  hoare [CollapsedLiveCapabilityApplicationGame.main_with_fixed_bit :
       arg.`4 = false
    ==>
       res.`mpge_win
    /\ res.`mpge_eligible
    /\ ! res.`mpge_guess
    /\ res.`mpge_live_query_count = 0
    /\ res.`mpge_live_challenge_count = 1
    /\ res.`mpge_history_query_count = 0
    /\ res.`mpge_history_capability_query_count = 1].
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
    /collapsed_capability_material /live_capability_materials_equal
    /capability_control_live_material /capability_control_history_material
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

lemma collapsed_live_capability_application_game_probability_one
    &m
    (initial_state : protocol_state)
    (initial_facts : signed_authorization_fact list)
    (retention_kappa : int) :
  Pr[
    CollapsedLiveCapabilityApplicationGame.main(
      initial_state, initial_facts, retention_kappa
    ) @ &m : res
  ] = 1%r.
proof.
  byphoare => //.
  proc.
  inline CollapsedLiveCapabilityApplicationGame.main_with_evidence.
  seq 1 : true 1%r 1%r 0%r 0%r.
  + rnd.
  + case (hidden_bit).
    + call collapsed_live_capability_application_fixed_real.
      auto.
    + call collapsed_live_capability_application_fixed_random.
      auto.
qed.

lemma collapsed_live_capability_application_normalized_advantage_half
    &m
    (initial_state : protocol_state)
    (initial_facts : signed_authorization_fact list)
    (retention_kappa : int) :
  mdprf_normalized_advantage
    (Pr[
       CollapsedLiveCapabilityApplicationGame.main(
         initial_state, initial_facts, retention_kappa
       ) @ &m : res
     ])
    1%r = 1%r / 2%r.
proof.
  rewrite collapsed_live_capability_application_game_probability_one.
  rewrite /mdprf_normalized_advantage.
  by smt().
qed.
