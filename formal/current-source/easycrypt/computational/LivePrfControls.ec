require import AllCore List FSet Distr.
require import ProtocolTypes ProtocolChecks CanonicalEncoding.
require import LiveKeyGame LivePrfTypes LivePrfGame.

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
proof.
  proc.
  inline *.
  auto.
  rewrite /prf_control_key_guesses_real /prf_control_secret
    /prf_control_live_label /prf_control_reveal_label /test_live_material
    /mdprf_live_query_count /mdprf_live_challenge_count
    /mdprf_query_is_live_query /mdprf_query_is_live_challenge
    /mdprf_kind_is_live_query /mdprf_kind_is_live_challenge /=.
  by smt().
qed.

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
proof.
  proc.
  inline *.
  auto.
  rewrite /prf_control_key_guesses_real /prf_control_secret
    /prf_control_live_label /prf_control_reveal_label
    /prf_control_history_label
    /test_live_material /test_history_material
    /mdprf_live_query_count /mdprf_live_challenge_count
    /mdprf_history_query_count
    /mdprf_history_capability_query_count
    /mdprf_query_is_live_query /mdprf_query_is_live_challenge
    /mdprf_query_is_history /mdprf_query_is_history_capability
    /mdprf_kind_is_live_query /mdprf_kind_is_live_challenge
    /mdprf_kind_is_history /mdprf_kind_is_history_capability /=.
  by smt().
qed.

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
proof.
  proc.
  inline *.
  auto.
  rewrite /prf_control_key_guesses_real /prf_control_secret
    /prf_control_live_label /prf_control_reveal_label
    /prf_control_history_label
    /test_live_material /test_history_material
    /mdprf_live_query_count /mdprf_live_challenge_count
    /mdprf_history_query_count
    /mdprf_history_capability_query_count
    /mdprf_query_is_live_query /mdprf_query_is_live_challenge
    /mdprf_query_is_history /mdprf_query_is_history_capability
    /mdprf_kind_is_live_query /mdprf_kind_is_live_challenge
    /mdprf_kind_is_history /mdprf_kind_is_history_capability /=.
  by smt().
qed.

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
  byphoare => //.
  proc.
  inline PrfControlGame.main_with_evidence.
  seq 1 : true 1%r 1%r 0%r 0%r.
  + rnd.
  + case (hidden_bit).
    + call prf_control_fixed_real.
      auto.
    + call prf_control_fixed_random.
      auto.
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
