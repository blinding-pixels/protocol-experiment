require import AllCore List FSet.
require import ProtocolTypes ProtocolChecks CanonicalEncoding ProtocolPrimitives.
require import AuthorizationState AuthorizationAncestry UnauthorizedOriginGame.
require import LiveKeyGame LiveKeyWitnesses.
require import LivePrfTypes LivePrfGame LivePrfApplicationReduction LivePrfControls.

type application_prf_trace_control_result = {
  aptc_evidence : mdprf_game_evidence;
  aptc_reveal_real : bool;
  aptc_challenge_real : bool;
  aptc_history_reached : bool
}.

(* Concrete application adversary used only as an end-to-end connectivity
   control.  It reveals a live key at node 1, then asks both history domains and
   challenges the distinct node 2.  The application exclusion therefore holds
   without exposing the challenge input through the reveal path. *)
module ApplicationPrfTraceAdversary(
  O : LIVE_PROTOCOL_ORACLE
) = {
  var reveal_was_real : bool
  var challenge_was_real : bool
  var history_reached : bool

  proc attack() : unit = {
    var created : node_id option;
    var updated : node_id option;
    var revealed : live_application_key option;
    var history : history_domain_output option;
    var capability : history_capability_output option;
    var challenged : live_application_key option;

    reveal_was_real <- false;
    challenge_was_real <- false;
    history_reached <- false;

    created <@ O.create_group(live_witness_creator, fset0);
    updated <@ O.send_beekem_update(live_witness_creator);
    revealed <@ O.reveal_live_key(live_witness_creator, NodeId 1);
    history <@ O.reveal_history_output(
      live_witness_creator, NodeId 2, SegmentId 908
    );
    capability <@ O.reveal_history_capability(
      live_witness_creator, NodeId 2, SegmentId 908, fset0
    );
    challenged <@ O.challenge_live(live_witness_creator, NodeId 2);

    if (revealed <> None) {
      reveal_was_real <-
        prf_control_key_guesses_real (oget revealed);
    }
    if (challenged <> None) {
      challenge_was_real <-
        prf_control_key_guesses_real (oget challenged);
    }
    history_reached <- history <> None /\ capability <> None;
  }

  proc guess() : bool = {
    return challenge_was_real;
  }
}.

module ApplicationPrfTraceGame = MultiDomainPrfGame(
  BPRFLive(
    ApplicationPrfTraceAdversary,
    TestSignature,
    TestNodeHash,
    TestBeeKemLiveRuntime
  ),
  TestMultiDomainKeySchedule,
  TestLiveKeySampler
).

module ApplicationPrfTraceControl = {
  proc main(bit : bool) : application_prf_trace_control_result = {
    var evidence : mdprf_game_evidence;

    evidence <@ ApplicationPrfTraceGame.main_with_fixed_bit(
      live_witness_protocol_state,
      [],
      1,
      bit
    );

    return
      {| aptc_evidence = evidence;
         aptc_reveal_real =
           ApplicationPrfTraceGame.A.A.reveal_was_real;
         aptc_challenge_real =
           ApplicationPrfTraceGame.A.A.challenge_was_real;
         aptc_history_reached =
           ApplicationPrfTraceGame.A.A.history_reached |};
  }
}.

lemma application_prf_random_trace_reaches_every_oracle :
  hoare [ApplicationPrfTraceControl.main :
       arg = false
    ==>
       (res.`aptc_evidence).`mpge_win
    /\ (res.`aptc_evidence).`mpge_eligible
    /\ ! (res.`aptc_evidence).`mpge_guess
    /\ res.`aptc_reveal_real
    /\ ! res.`aptc_challenge_real
    /\ res.`aptc_history_reached
    /\ (res.`aptc_evidence).`mpge_live_query_count = 1
    /\ (res.`aptc_evidence).`mpge_live_challenge_count = 1
    /\ (res.`aptc_evidence).`mpge_history_query_count = 1
    /\ (res.`aptc_evidence).`mpge_history_capability_query_count = 1].
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