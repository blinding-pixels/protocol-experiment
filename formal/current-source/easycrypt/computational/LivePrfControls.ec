require import AllCore List FSet Distr.
require import ProtocolTypes ProtocolChecks CanonicalEncoding.
require import LiveKeyGame LivePrfTypes LivePrfGame.

op prf_control_secret : beekem_secret = BeeKemSecret 100.

op prf_control_live_label : live_key_label =
  {| lkl_protocol_version = expected_protocol_version;
     lkl_document_id = DocumentId 903;
     lkl_node_id = NodeId 904;
     lkl_authorization_digest = AuthorizationDigest 906 |}.

op prf_control_history_label : history_key_label =
  {| hkl_protocol_version = expected_protocol_version;
     hkl_document_id = DocumentId 903;
     hkl_segment_id = SegmentId 905;
     hkl_authorization_digest = AuthorizationDigest 906 |}.

op prf_control_key_guesses_real (key : live_application_key) : bool =
  with key = LiveApplicationKey material label => 0 <= material.

(* This adversary exercises the actual primitive game.  It makes one permitted
   history query, one permitted constrained-history query, and one live
   challenge.  The deliberately insecure test KDF is distinguishable from the
   test sampler by the sign of the returned material. *)
module InsecureKdfPrfAdversary(
  O : MULTI_DOMAIN_PRF_ORACLE
) = {
  proc attack(
    initial_state : protocol_state,
    initial_facts : signed_authorization_fact list,
    retention_kappa : int
  ) : mdprf_adversary_result = {
    var history : history_domain_output;
    var capability : history_capability_output;
    var challenge : live_application_key;
    var guess : bool;

    history <@ O.derive_history(
      prf_control_secret, prf_control_history_label
    );
    capability <@ O.derive_history_capability(
      prf_control_secret, prf_control_history_label, fset0
    );
    challenge <@ O.challenge_live(
      prf_control_secret, prf_control_live_label
    );
    guess <- prf_control_key_guesses_real challenge;

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
    /\ res.`mpge_live_challenge_count = 1
    /\ res.`mpge_history_query_count = 1
    /\ res.`mpge_history_capability_query_count = 1].
proof.
  proc.
  inline *.
  auto.
  rewrite /prf_control_key_guesses_real /prf_control_secret
    /prf_control_live_label /prf_control_history_label
    /test_live_material /test_history_material
    /mdprf_live_query_count /mdprf_history_query_count
    /mdprf_history_capability_query_count
    /mdprf_query_is_live /mdprf_query_is_history
    /mdprf_query_is_history_capability
    /mdprf_kind_is_live /mdprf_kind_is_history
    /mdprf_kind_is_history_capability /=.
  by smt().
qed.

lemma prf_control_fixed_random :
  hoare [PrfControlGame.main_with_fixed_bit :
    arg.`4 = false ==>
       res.`mpge_win
    /\ res.`mpge_eligible
    /\ ! res.`mpge_guess
    /\ res.`mpge_live_challenge_count = 1
    /\ res.`mpge_history_query_count = 1
    /\ res.`mpge_history_capability_query_count = 1].
proof.
  proc.
  inline *.
  auto.
  rewrite /prf_control_key_guesses_real /prf_control_secret
    /prf_control_live_label /prf_control_history_label
    /test_live_material /test_history_material
    /mdprf_live_query_count /mdprf_history_query_count
    /mdprf_history_capability_query_count
    /mdprf_query_is_live /mdprf_query_is_history
    /mdprf_query_is_history_capability
    /mdprf_kind_is_live /mdprf_kind_is_history
    /mdprf_kind_is_history_capability /=.
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
     ]) = 1%r / 2%r.
proof.
  rewrite insecure_test_kdf_prf_game_probability_one.
  rewrite /mdprf_normalized_advantage.
  by smt().
qed.