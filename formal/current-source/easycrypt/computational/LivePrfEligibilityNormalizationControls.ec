require import AllCore List FSet Distr.
require import ProtocolTypes CanonicalEncoding.
require import LiveKeyGame LivePrfTypes LivePrfGame.

(* Executable normalization control.  This adversary makes no oracle query and
   the challenger-visible eligibility result is false.  Both hidden-bit games
   therefore lose, and the normalized advantage must use zero eligibility mass
   as its baseline rather than subtracting an unconditional one half. *)
module IneligiblePrfAdversary(
  O : MULTI_DOMAIN_PRF_ORACLE
) = {
  proc attack(
    initial_state : protocol_state,
    initial_facts : signed_authorization_fact list,
    retention_kappa : int
  ) : mdprf_adversary_result = {
    return {| mpar_eligible = false; mpar_guess = true |};
  }
}.

module IneligiblePrfGame = MultiDomainPrfGame(
  IneligiblePrfAdversary,
  TestMultiDomainKeySchedule,
  TestLiveKeySampler
).

lemma ineligible_prf_fixed_real_loses :
  hoare [IneligiblePrfGame.main_with_fixed_bit :
       arg.`4 = true
    ==>
       ! res.`mpge_win
    /\ ! res.`mpge_eligible
    /\ res.`mpge_guess
    /\ res.`mpge_live_query_count = 0
    /\ res.`mpge_live_challenge_count = 0
    /\ res.`mpge_history_query_count = 0
    /\ res.`mpge_history_capability_query_count = 0].
proof.
  proc.
  inline *.
  auto.
  rewrite /mdprf_live_query_count /mdprf_live_challenge_count
    /mdprf_history_query_count
    /mdprf_history_capability_query_count /=.
  by done.
qed.

lemma ineligible_prf_fixed_random_loses :
  hoare [IneligiblePrfGame.main_with_fixed_bit :
       arg.`4 = false
    ==>
       ! res.`mpge_win
    /\ ! res.`mpge_eligible
    /\ res.`mpge_guess
    /\ res.`mpge_live_query_count = 0
    /\ res.`mpge_live_challenge_count = 0
    /\ res.`mpge_history_query_count = 0
    /\ res.`mpge_history_capability_query_count = 0].
proof.
  proc.
  inline *.
  auto.
  rewrite /mdprf_live_query_count /mdprf_live_challenge_count
    /mdprf_history_query_count
    /mdprf_history_capability_query_count /=.
  by done.
qed.

lemma ineligible_prf_main_never_wins
    (initial_state : protocol_state)
    (initial_facts : signed_authorization_fact list)
    (retention_kappa : int) :
  hoare [IneligiblePrfGame.main :
       arg = (initial_state, initial_facts, retention_kappa)
    ==>
       ! res].
proof.
  proc.
  inline *.
  auto.
qed.

lemma ineligible_prf_game_probability_zero
    &m
    (initial_state : protocol_state)
    (initial_facts : signed_authorization_fact list)
    (retention_kappa : int) :
  Pr[
    IneligiblePrfGame.main(
      initial_state, initial_facts, retention_kappa
    ) @ &m : res
  ] = 0%r.
proof.
  byphoare
    (_ : arg = (initial_state, initial_facts, retention_kappa) ==> ! res)
    => //=.
  exact (ineligible_prf_main_never_wins
    initial_state initial_facts retention_kappa).
qed.

lemma ineligible_prf_evidence_never_eligible
    (initial_state : protocol_state)
    (initial_facts : signed_authorization_fact list)
    (retention_kappa : int) :
  hoare [IneligiblePrfGame.main_with_evidence :
       arg = (initial_state, initial_facts, retention_kappa)
    ==>
       ! res.`mpge_eligible].
proof.
  proc.
  inline *.
  auto.
qed.

lemma ineligible_prf_eligibility_probability_zero
    &m
    (initial_state : protocol_state)
    (initial_facts : signed_authorization_fact list)
    (retention_kappa : int) :
  Pr[
    IneligiblePrfGame.main_with_evidence(
      initial_state, initial_facts, retention_kappa
    ) @ &m : res.`mpge_eligible
  ] = 0%r.
proof.
  byphoare
    (_ : arg = (initial_state, initial_facts, retention_kappa) ==>
         ! res.`mpge_eligible)
    => //=.
  exact (ineligible_prf_evidence_never_eligible
    initial_state initial_facts retention_kappa).
qed.

lemma ineligible_prf_normalized_advantage_zero
    &m
    (initial_state : protocol_state)
    (initial_facts : signed_authorization_fact list)
    (retention_kappa : int) :
  mdprf_normalized_advantage
    (Pr[
       IneligiblePrfGame.main(
         initial_state, initial_facts, retention_kappa
       ) @ &m : res
     ])
    (Pr[
       IneligiblePrfGame.main_with_evidence(
         initial_state, initial_facts, retention_kappa
       ) @ &m : res.`mpge_eligible
     ]) = 0%r.
proof.
  rewrite ineligible_prf_game_probability_zero
    ineligible_prf_eligibility_probability_zero.
  rewrite /mdprf_normalized_advantage.
  by smt().
qed.
