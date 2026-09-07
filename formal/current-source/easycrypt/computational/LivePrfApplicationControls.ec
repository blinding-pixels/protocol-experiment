require import AllCore List FSet.
require import ProtocolTypes ProtocolChecks CanonicalEncoding ProtocolPrimitives.
require import AuthorizationState AuthorizationAncestry UnauthorizedOriginGame.
require import LiveKeyGame LiveKeyWitnesses.
require import LivePrfTypes LivePrfGame LivePrfApplicationReduction LivePrfControls.

(* The executable controls have one definition in LivePrfControls.  These
   aliases preserve the public module paths by definitional identity. *)
module ApplicationPrfTraceAdversary =
  LivePrfControls.ApplicationPrfTraceAdversary.
module ApplicationPrfTraceGame = LivePrfControls.ApplicationPrfTraceGame.

(* Known-invalid unrestricted claims retained below.  LivePrfControls proves
   probability-one counterexamples at retention zero, as well as an initialized
   positive witness.  Do not count this file as accepted until the unrestricted
   statements themselves have been resolved; importing them is not verification. *)

(* End-to-end non-vacuity control for the exact application/PRF hop.  The
   application trace is eligible, its public diagnostic bit confirms the real
   reveal / sampled challenge / reached-history conjunction, and the primitive
   transcript contains exactly one call in every application-relevant domain. *)
lemma application_prf_random_trace_reaches_every_oracle :
  hoare [ApplicationPrfTraceGame.main_with_fixed_bit :
       arg.`4 = false
    ==>
       res.`mpge_win
    /\ res.`mpge_eligible
    /\ ! res.`mpge_guess
    /\ res.`mpge_live_query_count = 1
    /\ res.`mpge_live_challenge_count = 1
    /\ res.`mpge_history_query_count = 1
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
    /test_history_material /test_live_material
    /prf_control_key_guesses_real
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

module ApplicationRejectedChallengeAdversary =
  LivePrfControls.ApplicationRejectedChallengeAdversary.
module ApplicationRejectedChallengeGame =
  LivePrfControls.ApplicationRejectedChallengeGame.

(* The failed application challenge consumes no primitive challenge, and the
   challenger-owned switch is closed before the later reveal.  Otherwise the
   final evidence would contain more than one primitive challenge, fewer than
   two real-only reveals, or a true diagnostic guess. *)
lemma rejected_application_challenge_preserves_prf_routing :
  hoare [ApplicationRejectedChallengeGame.main_with_fixed_bit :
       arg.`4 = false
    ==>
       res.`mpge_win
    /\ res.`mpge_eligible
    /\ ! res.`mpge_guess
    /\ res.`mpge_live_query_count = 2
    /\ res.`mpge_live_challenge_count = 1
    /\ res.`mpge_history_query_count = 0
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
    /test_history_material /test_live_material
    /prf_control_key_guesses_real
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

(* Multi-challenge counter control.  Two distinct accepted application
   challenges must remain two distinct primitive PRF challenge calls.  This is
   the application-side non-hardcoding witness needed before the authoritative
   BeeKEM challenge counter can be related to the theorem's [c] parameter. *)
module ApplicationTwoChallengeAdversary(
  O : LIVE_PROTOCOL_ORACLE
) = {
  var first_challenge_reached : bool
  var second_challenge_reached : bool

  proc attack() : unit = {
    var created : node_id option;
    var update_two : node_id option;
    var update_three : node_id option;
    var first_challenge : live_application_key option;
    var second_challenge : live_application_key option;

    first_challenge_reached <- false;
    second_challenge_reached <- false;

    created <@ O.create_group(live_witness_creator, fset0);
    update_two <@ O.send_beekem_update(live_witness_creator);
    first_challenge <@ O.challenge_live(
      live_witness_creator, NodeId 2
    );
    update_three <@ O.send_beekem_update(live_witness_creator);
    second_challenge <@ O.challenge_live(
      live_witness_creator, NodeId 3
    );

    first_challenge_reached <- first_challenge <> None;
    second_challenge_reached <- second_challenge <> None;
  }

  (* False records the expected successful two-challenge trace in the random
     primitive world. *)
  proc guess() : bool = {
    return ! (first_challenge_reached /\ second_challenge_reached);
  }
}.

module ApplicationTwoChallengeGame = MultiDomainPrfGame(
  BPRFLive(
    ApplicationTwoChallengeAdversary,
    TestSignature,
    TestNodeHash,
    TestBeeKemLiveRuntime
  ),
  TestMultiDomainKeySchedule,
  TestLiveKeySampler
).

lemma two_accepted_application_challenges_map_to_two_prf_challenges :
  hoare [ApplicationTwoChallengeGame.main_with_fixed_bit :
       initial_state = live_witness_protocol_state
    /\ initial_facts = []
    /\ retention_kappa = 1
    /\ hidden_bit = false
    ==>
       res.`mpge_win
    /\ res.`mpge_eligible
    /\ ! res.`mpge_guess
    /\ res.`mpge_live_query_count = 0
    /\ res.`mpge_live_challenge_count = 2
    /\ res.`mpge_history_query_count = 0
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
    /live_label_of /test_live_material
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
