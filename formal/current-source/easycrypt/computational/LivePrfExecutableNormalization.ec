require import AllCore List Distr DBool.
require import ProtocolTypes CanonicalEncoding LiveKeyGame.
require import LivePrfTypes LivePrfGame.

(* Kernel connection between the executable fair-bit game and its two fixed-bit
   executions.  This is intentionally independent of the BeeKEM adapter: it
   reasons only about the already-defined multi-domain PRF game. *)
section ExecutableMultiDomainPrfNormalization.
  declare module A <: MULTI_DOMAIN_PRF_ADVERSARY.
  declare module K <: MULTI_DOMAIN_KEY_SCHEDULE.
  declare module R <: LIVE_KEY_SAMPLER.

  module G = MultiDomainPrfGame(A, K, R).

  type mdprf_execution_input =
    protocol_state * signed_authorization_fact list * int.

  local module FairBitRunner = {
    var sampled_bit : bool

    proc main(input : mdprf_execution_input) : bool = {
      var evidence : mdprf_game_evidence;

      sampled_bit <$ dbool;
      if (sampled_bit) {
        evidence <@ G.main_with_fixed_bit(
          input.`1, input.`2, input.`3, true
        );
      } else {
        evidence <@ G.main_with_fixed_bit(
          input.`1, input.`2, input.`3, false
        );
      }
      return evidence.`mpge_win;
    }
  }.

  lemma mdprf_sampled_game_equiv_fair_bit_runner
      &m
      (initial_state : protocol_state)
      (initial_facts : signed_authorization_fact list)
      (retention_kappa : int) :
    Pr[
      G.main(initial_state, initial_facts, retention_kappa) @ &m : res
    ] =
    Pr[
      FairBitRunner.main(
        initial_state, initial_facts, retention_kappa
      ) @ &m : res
    ].
  proof.
    byequiv => //.
    proc.
    inline G.main_with_evidence.
    rnd.
    if{2}; call (_ : true); auto.
  qed.

  lemma mdprf_sampled_win_probability_is_fixed_bit_average
      &m
      (initial_state : protocol_state)
      (initial_facts : signed_authorization_fact list)
      (retention_kappa : int) :
    Pr[
      G.main(initial_state, initial_facts, retention_kappa) @ &m : res
    ] =
      (Pr[
         G.main_with_fixed_bit(
           initial_state, initial_facts, retention_kappa, true
         ) @ &m : res.`mpge_win
       ] +
       Pr[
         G.main_with_fixed_bit(
           initial_state, initial_facts, retention_kappa, false
         ) @ &m : res.`mpge_win
       ]) / 2%r.
  proof.
    rewrite mdprf_sampled_game_equiv_fair_bit_runner.
    have -> :
      Pr[
        FairBitRunner.main(
          initial_state, initial_facts, retention_kappa
        ) @ &m : res
      ] =
      Pr[
        FairBitRunner.main(
          initial_state, initial_facts, retention_kappa
        ) @ &m : res /\ FairBitRunner.sampled_bit
      ] +
      Pr[
        FairBitRunner.main(
          initial_state, initial_facts, retention_kappa
        ) @ &m : res /\ ! FairBitRunner.sampled_bit
      ].
    + by rewrite Pr[mu_split FairBitRunner.sampled_bit].

    have Htrue :
      Pr[
        FairBitRunner.main(
          initial_state, initial_facts, retention_kappa
        ) @ &m : res /\ FairBitRunner.sampled_bit
      ] =
      1%r / 2%r *
      Pr[
        G.main_with_fixed_bit(
          initial_state, initial_facts, retention_kappa, true
        ) @ &m : res.`mpge_win
      ].
    + byphoare (_ :
          (glob G) = (glob G){m}
       /\ input = (initial_state, initial_facts, retention_kappa)
       ==>
          res /\ FairBitRunner.sampled_bit) => //.
      proc.
      pose p := Pr[
        G.main_with_fixed_bit(
          initial_state, initial_facts, retention_kappa, true
        ) @ &m : res.`mpge_win
      ].
      seq 1 :
        (FairBitRunner.sampled_bit = true /\
         input = (initial_state, initial_facts, retention_kappa))
        (1%r / 2%r) p _ 0%r
        ((glob G) = (glob G){m} /\
         input = (initial_state, initial_facts, retention_kappa));
        first by auto.
      + by rnd (pred1 true); skip => />; rewrite dbool1E.
      + if; last by (conseq (_ : false ==> _); 1:by smt()); auto.
        conseq (_ : _ ==> evidence.`mpge_win) => //; first by smt().
        call (_ :
          input = (initial_state, initial_facts, retention_kappa) /\
          (glob G) = (glob G){m}
          ==> res.`mpge_win); last by auto.
        by bypr => &m0 hm0; rewrite /p; byequiv => //; proc (true).
      + by (conseq (_ : _ ==> false); 1:smt()); auto.
      smt().

    have Hfalse :
      Pr[
        FairBitRunner.main(
          initial_state, initial_facts, retention_kappa
        ) @ &m : res /\ ! FairBitRunner.sampled_bit
      ] =
      1%r / 2%r *
      Pr[
        G.main_with_fixed_bit(
          initial_state, initial_facts, retention_kappa, false
        ) @ &m : res.`mpge_win
      ].
    + byphoare (_ :
          (glob G) = (glob G){m}
       /\ input = (initial_state, initial_facts, retention_kappa)
       ==>
          res /\ ! FairBitRunner.sampled_bit) => //.
      proc.
      pose p := Pr[
        G.main_with_fixed_bit(
          initial_state, initial_facts, retention_kappa, false
        ) @ &m : res.`mpge_win
      ].
      seq 1 :
        (FairBitRunner.sampled_bit = false /\
         input = (initial_state, initial_facts, retention_kappa))
        (1%r / 2%r) p _ 0%r
        ((glob G) = (glob G){m} /\
         input = (initial_state, initial_facts, retention_kappa));
        first by auto.
      + by rnd (pred1 false); skip => />; rewrite dbool1E.
      + if; first by (conseq (_ : false ==> _); 1:by smt()); auto.
        conseq (_ : _ ==> evidence.`mpge_win) => //; first by smt().
        call (_ :
          input = (initial_state, initial_facts, retention_kappa) /\
          (glob G) = (glob G){m}
          ==> res.`mpge_win); last by auto.
        by bypr => &m0 hm0; rewrite /p; byequiv => //; proc (true).
      + by (conseq (_ : _ ==> false); 1:smt()); auto.
      smt().

    rewrite Htrue Hfalse.
    smt().
  qed.
end section ExecutableMultiDomainPrfNormalization.
