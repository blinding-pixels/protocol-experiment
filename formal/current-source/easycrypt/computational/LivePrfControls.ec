require import AllCore List FSet Distr.
require import ProtocolTypes ProtocolChecks CanonicalEncoding ProtocolPrimitives.
require import AuthorizationState AuthorizationAncestry UnauthorizedOriginGame.
require import LiveKeyGame LiveKeyWitnesses LivePrfTypes LivePrfGame.
require import LivePrfApplicationReduction.

op prf_control_secret : beekem_secret = BeeKemSecret 100.

op prf_control_live_label : live_key_label =
  {| lkl_protocol_version = expected_protocol_version;
     lkl_document_id = DocumentId 903;
     lkl_node_id = NodeId 904;
     lkl_authorization_digest = AuthorizationDigest 906 |}.

op prf_control_reveal_label : live_key_label =
  {| lkl_protocol_version = expected_protocol_version;
     lkl_document_id = DocumentId 903;
     lkl_node_id = NodeId 907;
     lkl_authorization_digest = AuthorizationDigest 906 |}.

lemma prf_control_reveal_and_challenge_labels_differ :
  prf_control_reveal_label <> prf_control_live_label.
proof. by done. qed.

op prf_control_history_label : history_key_label =
  {| hkl_protocol_version = expected_protocol_version;
     hkl_document_id = DocumentId 903;
     hkl_segment_id = SegmentId 905;
     hkl_authorization_digest = AuthorizationDigest 906 |}.

op prf_control_key_guesses_real (key : live_application_key) : bool =
  with key = LiveApplicationKey material label => 0 <= material.

(* Direct separation control.  Even in the random challenge world, a permitted
   live reveal is derived by the real key schedule while the distinguished live
   challenge is sampled. *)
module PrfRevealChallengeControl = {
  module O = MultiDomainPrfOracle(
    TestMultiDomainKeySchedule,
    TestLiveKeySampler
  )

  proc main(bit : bool) : live_application_key * live_application_key = {
    var revealed : live_application_key;
    var challenged : live_application_key;

    O.init(bit);
    revealed <@ O.derive_live(
      prf_control_secret, prf_control_reveal_label
    );
    challenged <@ O.challenge_live(
      prf_control_secret, prf_control_live_label
    );
    return (revealed, challenged);
  }
}.

lemma prf_random_world_keeps_reveal_real :
  hoare [PrfRevealChallengeControl.main :
       arg = false
    ==>
       prf_control_key_guesses_real res.`1
    /\ ! prf_control_key_guesses_real res.`2
    /\ mdprf_live_query_count
         PrfRevealChallengeControl.O.queries = 1
    /\ mdprf_live_challenge_count
         PrfRevealChallengeControl.O.queries = 1].
proof. by proc; inline *; auto. qed.

(* This adversary exercises every application-relevant primitive path.  It
   makes one permitted live reveal, one permitted history query, one permitted
   constrained-history query, and one distinguished live challenge.  The
   deliberately insecure test KDF is distinguishable from the test sampler by
   the sign of the challenge material; requiring the reveal to remain real
   detects accidental challenge routing of ordinary live queries. *)
module InsecureKdfPrfAdversary(
  O : MULTI_DOMAIN_PRF_ORACLE
) = {
  proc attack(
    initial_state : protocol_state,
    initial_facts : signed_authorization_fact list,
    retention_kappa : int
  ) : mdprf_adversary_result = {
    var revealed : live_application_key;
    var history : history_domain_output;
    var capability : history_capability_output;
    var challenge : live_application_key;
    var guess : bool;

    revealed <@ O.derive_live(
      prf_control_secret, prf_control_reveal_label
    );
    history <@ O.derive_history(
      prf_control_secret, prf_control_history_label
    );
    capability <@ O.derive_history_capability(
      prf_control_secret, prf_control_history_label, fset0
    );
    challenge <@ O.challenge_live(
      prf_control_secret, prf_control_live_label
    );
    guess <-
         prf_control_key_guesses_real revealed
      /\ prf_control_key_guesses_real challenge;

    return {| mpar_eligible = true; mpar_guess = guess |};
  }
}.

module PrfControlGame = MultiDomainPrfGame(
  InsecureKdfPrfAdversary,
  TestMultiDomainKeySchedule,
  TestLiveKeySampler
).

lemma prf_control_fixed_real :
  hoare [PrfControlGame.main_with_fixed_bit :
    arg.`4 = true ==>
       res.`mpge_win
    /\ res.`mpge_eligible
    /\ res.`mpge_guess
    /\ res.`mpge_live_query_count = 1
    /\ res.`mpge_live_challenge_count = 1
    /\ res.`mpge_history_query_count = 1
    /\ res.`mpge_history_capability_query_count = 1].
proof. by proc; inline *; auto. qed.

lemma prf_control_fixed_random :
  hoare [PrfControlGame.main_with_fixed_bit :
    arg.`4 = false ==>
       res.`mpge_win
    /\ res.`mpge_eligible
    /\ ! res.`mpge_guess
    /\ res.`mpge_live_query_count = 1
    /\ res.`mpge_live_challenge_count = 1
    /\ res.`mpge_history_query_count = 1
    /\ res.`mpge_history_capability_query_count = 1].
proof. by proc; inline *; auto. qed.

lemma insecure_test_kdf_prf_game_probability_one
    &m
    (initial_state : protocol_state)
    (initial_facts : signed_authorization_fact list)
    (retention_kappa : int) :
  Pr[
    PrfControlGame.main(
      initial_state, initial_facts, retention_kappa
    ) @ &m : res
  ] = 1%r.
proof.
  byphoare => //; proc; inline *; auto.
  rewrite DBool.dbool_ll /prf_control_key_guesses_real
    /prf_control_secret /prf_control_live_label /prf_control_reveal_label
    /test_live_material /=.
  by smt().
qed.

lemma insecure_test_kdf_prf_normalized_advantage_half
    &m
    (initial_state : protocol_state)
    (initial_facts : signed_authorization_fact list)
    (retention_kappa : int) :
  mdprf_normalized_advantage
    (Pr[
       PrfControlGame.main(
         initial_state, initial_facts, retention_kappa
       ) @ &m : res
     ])
    1%r = 1%r / 2%r.
proof.
  rewrite insecure_test_kdf_prf_game_probability_one.
  rewrite /mdprf_normalized_advantage.
  by smt().
qed.

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

  (* In the primitive random world this public bit is false exactly when the
     application reveal stayed real, the distinguished challenge was sampled,
     and both history procedures returned outputs. *)
  proc guess() : bool = {
    return
         ! reveal_was_real
      \/ challenge_was_real
      \/ ! history_reached;
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


(* This control forces the challenge wrapper through its rejected branch and
   then continues using the same key-schedule adapter.  A reveal of node 2
   makes the immediately following challenge of node 2 invalid.  The trace then
   reveals node 3 and challenges node 4.  In the random world, both reveals must
   remain real and only the final accepted challenge may be sampled. *)
module ApplicationRejectedChallengeAdversary(
  O : LIVE_PROTOCOL_ORACLE
) = {
  var first_reveal_real : bool
  var rejected_challenge_was_none : bool
  var second_reveal_real : bool
  var final_challenge_real : bool

  proc attack() : unit = {
    var created : node_id option;
    var update_two : node_id option;
    var update_three : node_id option;
    var update_four : node_id option;
    var first_reveal : live_application_key option;
    var rejected_challenge : live_application_key option;
    var second_reveal : live_application_key option;
    var final_challenge : live_application_key option;

    first_reveal_real <- false;
    rejected_challenge_was_none <- false;
    second_reveal_real <- false;
    final_challenge_real <- false;

    created <@ O.create_group(live_witness_creator, fset0);
    update_two <@ O.send_beekem_update(live_witness_creator);
    first_reveal <@ O.reveal_live_key(
      live_witness_creator, NodeId 2
    );
    rejected_challenge <@ O.challenge_live(
      live_witness_creator, NodeId 2
    );
    update_three <@ O.send_beekem_update(live_witness_creator);
    second_reveal <@ O.reveal_live_key(
      live_witness_creator, NodeId 3
    );
    update_four <@ O.send_beekem_update(live_witness_creator);
    final_challenge <@ O.challenge_live(
      live_witness_creator, NodeId 4
    );

    if (first_reveal <> None) {
      first_reveal_real <-
        prf_control_key_guesses_real (oget first_reveal);
    }
    rejected_challenge_was_none <- rejected_challenge = None;
    if (second_reveal <> None) {
      second_reveal_real <-
        prf_control_key_guesses_real (oget second_reveal);
    }
    if (final_challenge <> None) {
      final_challenge_real <-
        prf_control_key_guesses_real (oget final_challenge);
    }
  }

  (* False records the complete expected random-world routing outcome. *)
  proc guess() : bool = {
    return
         ! first_reveal_real
      \/ ! rejected_challenge_was_none
      \/ ! second_reveal_real
      \/ final_challenge_real;
  }
}.

module ApplicationRejectedChallengeGame = MultiDomainPrfGame(
  BPRFLive(
    ApplicationRejectedChallengeAdversary,
    TestSignature,
    TestNodeHash,
    TestBeeKemLiveRuntime
  ),
  TestMultiDomainKeySchedule,
  TestLiveKeySampler
).


(* A terminating execution of the exact application control with retention
   zero refutes the unrestricted positive eligibility claim. *)
lemma application_prf_zero_retention_is_ineligible :
  phoare [ApplicationPrfTraceGame.main_with_fixed_bit :
       arg = (live_witness_protocol_state, [], 0, false)
    ==>
       ! res.`mpge_eligible /\ ! res.`mpge_win] = 1%r.
proof. by proc; inline *; auto. qed.

lemma rejected_application_prf_zero_retention_is_ineligible :
  phoare [ApplicationRejectedChallengeGame.main_with_fixed_bit :
       arg = (live_witness_protocol_state, [], 0, false)
    ==>
       ! res.`mpge_eligible /\ ! res.`mpge_win] = 1%r.
proof. by proc; inline *; auto. qed.


lemma application_prf_zero_retention_counterexample &m :
  Pr[ApplicationPrfTraceGame.main_with_fixed_bit(
      live_witness_protocol_state, [], 0, false) @ &m :
      ! res.`mpge_eligible /\ ! res.`mpge_win] = 1%r.
proof. byphoare application_prf_zero_retention_is_ineligible => //. qed.

lemma rejected_application_prf_zero_retention_counterexample &m :
  Pr[ApplicationRejectedChallengeGame.main_with_fixed_bit(
      live_witness_protocol_state, [], 0, false) @ &m :
      ! res.`mpge_eligible /\ ! res.`mpge_win] = 1%r.
proof. byphoare rejected_application_prf_zero_retention_is_ineligible => //. qed.

(* Explicitly initialized positive witness for the same executable control.
   This new probability-one statement is not a repair or replacement of the
   unrestricted claim in LivePrfApplicationControls. *)
lemma initialized_application_prf_random_trace_reaches_every_oracle :
  phoare [ApplicationPrfTraceGame.main_with_fixed_bit :
    arg = (live_witness_protocol_state, [], 1, false)
    ==> res.`mpge_win /\ res.`mpge_eligible /\ ! res.`mpge_guess
    /\ res.`mpge_live_query_count = 1
    /\ res.`mpge_live_challenge_count = 1
    /\ res.`mpge_history_query_count = 1
    /\ res.`mpge_history_capability_query_count = 1] = 1%r.
proof.
  proc; inline *; auto.
  move=> &hr [-> [-> [-> ->]]].
  rewrite /live_witness_protocol_state /= ?inE /=.
  rewrite /all_nodes_known /all_predecessors_delivered
    ?elems_fset0 ?elems_fset1
    /all_nodes_known_list /all_predecessors_delivered_list /= ?inE /=.
  rewrite /active_member_store_put /active_member_store_of_set
    /node_digest_store_put /member_secret_store_put /delivery_store_put
    /empty_node_digest_store /empty_member_secret_store
    /empty_delivery_store /empty_active_member_store /= ?inE /=.
  rewrite /all_nodes_known /all_predecessors_delivered
    ?elems_fset0 ?elems_fset1
    /all_nodes_known_list /all_predecessors_delivered_list /= ?inE /=.
  rewrite /live_initial_authorization /authorization_policy_replay
    /authorization_policy_replay_from /=.
  rewrite /live_trace_admissible /challenge_query_count /query_is_challenge
    /bee_safe_kappa /every_challenge_safe /query_challenge_member
    /every_compromise_safe_for_challenge /query_compromise_member /=.
  rewrite /query_compromise_member /query_challenge_member
    /query_is_challenge /=.
  rewrite /prf_control_key_guesses_real /test_live_material /live_label_of
    /live_initial_authorization_digest /=.
  rewrite /mdprf_live_query_count /mdprf_live_challenge_count
    /mdprf_history_query_count /mdprf_history_capability_query_count
    /mdprf_query_is_live_query /mdprf_query_is_live_challenge
    /mdprf_query_is_history /mdprf_query_is_history_capability
    /mdprf_kind_is_live_query /mdprf_kind_is_live_challenge
    /mdprf_kind_is_history /mdprf_kind_is_history_capability /=.
  by rewrite /mdprf_query_is_live_query /mdprf_query_is_live_challenge
    /mdprf_query_is_history /mdprf_query_is_history_capability
    /mdprf_kind_is_live_query /mdprf_kind_is_live_challenge
    /mdprf_kind_is_history /mdprf_kind_is_history_capability /=.
qed.
