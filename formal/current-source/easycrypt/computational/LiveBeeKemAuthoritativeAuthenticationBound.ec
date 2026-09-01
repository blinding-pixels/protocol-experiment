require import AllCore List FSet Distr.
require import ProtocolTypes ProtocolPrimitives.
require import LiveKeyGame LivePrfGame.
require import BeeKemConstruction.
require import LiveBeeKemAuthoritativeLiveTypes.
require import LiveBeeKemAuthoritativeAuthentication.

(* The public application advantage is the ordinary centered hidden-bit
   advantage.  Ineligible executions return the deterministic decision bit
   false, which contributes only the fair-game baseline; they are not silently
   discarded or charged as a distinguishing win. *)
op authoritative_live_normalized_advantage
    (success_probability : real) : real =
  mdprf_normalized_advantage success_probability 1%r.

lemma authoritative_live_normalized_advantage_perturbation
    (raw_success authenticated_success failure_probability : real) :
  0%r <= failure_probability =>
  raw_success <= authenticated_success + failure_probability =>
  authenticated_success <= raw_success + failure_probability =>
  authoritative_live_normalized_advantage raw_success <=
    authoritative_live_normalized_advantage authenticated_success +
    failure_probability.
proof.
  move=> Hfailure Hraw Hauthenticated.
  rewrite /authoritative_live_normalized_advantage
    /mdprf_normalized_advantage.
  case (1%r / 2%r <= raw_success);
  case (1%r / 2%r <= authenticated_success);
  smt().
qed.

lemma authoritative_live_evidence_agrees_without_authentication_failure
    (core : authoritative_live_application_core_evidence)
    (authentication_failure : bool) :
  ! authentication_failure =>
  (authoritative_live_application_evidence_of
     core authentication_failure).`alae_raw_win =
  (authoritative_live_application_evidence_of
     core authentication_failure).`alae_authenticated_win.
proof.
  rewrite /authoritative_live_application_evidence_of
    /authoritative_live_core_authenticated_eligible
    /authoritative_live_authenticated_eligible.
  by smt().
qed.

section AuthoritativeLiveAuthenticationAdvantage.
  declare module A <: AUTHORITATIVE_LIVE_KEY_ADVERSARY.
  declare module S <: SIGNATURE_SCHEME.
  declare module H <: NODE_HASH.
  declare module K <: MULTI_DOMAIN_KEY_SCHEDULE.
  declare module R <: LIVE_KEY_SAMPLER.
  declare module I <: BEEKEM_PAPER_INSTANCE.

  module L0 = AuthoritativeLiveRealGame(A, S, H, K, R, I).

  lemma authoritative_live_raw_authenticated_agree_without_failure :
    hoare[
      L0.main_with_evidence :
      true ==>
      ! res.`alae_authentication_failure =>
      res.`alae_raw_win = res.`alae_authenticated_win
    ].
  proof.
    proc.
    inline L0.SO.init L0.O.init.
    call (_ : true).
    auto=> />.
    exact authoritative_live_evidence_agrees_without_authentication_failure.
  qed.

  lemma authoritative_live_raw_authenticated_difference_zero
      &m :
    Pr[
      L0.main_with_evidence() @ &m :
        res.`alae_raw_win <> res.`alae_authenticated_win /\
        ! res.`alae_authentication_failure
    ] = 0%r.
  proof.
    byphoare
      (_ : true ==>
        ! (res.`alae_raw_win <> res.`alae_authenticated_win /\
           ! res.`alae_authentication_failure)) => //=.
    conseq authoritative_live_raw_authenticated_agree_without_failure => /#.
  qed.

  lemma authoritative_live_raw_success_le_authenticated_plus_failure
      &m :
    Pr[
      L0.main_with_evidence() @ &m : res.`alae_raw_win
    ] <=
    Pr[
      L0.main_with_evidence() @ &m : res.`alae_authenticated_win
    ] +
    Pr[
      L0.main_with_evidence() @ &m : res.`alae_authentication_failure
    ].
  proof.
    have Hsub :
      Pr[L0.main_with_evidence() @ &m : res.`alae_raw_win] <=
      Pr[
        L0.main_with_evidence() @ &m :
          (res.`alae_authenticated_win \/
           res.`alae_authentication_failure) \/
          (res.`alae_raw_win <> res.`alae_authenticated_win /\
           ! res.`alae_authentication_failure)
      ].
    + rewrite Pr[mu_sub]=> /#.

    have Hunion :
      Pr[
        L0.main_with_evidence() @ &m :
          (res.`alae_authenticated_win \/
           res.`alae_authentication_failure) \/
          (res.`alae_raw_win <> res.`alae_authenticated_win /\
           ! res.`alae_authentication_failure)
      ] <=
      Pr[L0.main_with_evidence() @ &m : res.`alae_authenticated_win] +
      Pr[L0.main_with_evidence() @ &m : res.`alae_authentication_failure] +
      Pr[
        L0.main_with_evidence() @ &m :
          res.`alae_raw_win <> res.`alae_authenticated_win /\
          ! res.`alae_authentication_failure
      ].
    + rewrite !mu_or.
      smt(ge0_mu).

    rewrite authoritative_live_raw_authenticated_difference_zero in Hunion.
    smt().
  qed.

  lemma authoritative_live_authenticated_success_le_raw_plus_failure
      &m :
    Pr[
      L0.main_with_evidence() @ &m : res.`alae_authenticated_win
    ] <=
    Pr[
      L0.main_with_evidence() @ &m : res.`alae_raw_win
    ] +
    Pr[
      L0.main_with_evidence() @ &m : res.`alae_authentication_failure
    ].
  proof.
    have Hsub :
      Pr[L0.main_with_evidence() @ &m : res.`alae_authenticated_win] <=
      Pr[
        L0.main_with_evidence() @ &m :
          (res.`alae_raw_win \/ res.`alae_authentication_failure) \/
          (res.`alae_raw_win <> res.`alae_authenticated_win /\
           ! res.`alae_authentication_failure)
      ].
    + rewrite Pr[mu_sub]=> /#.

    have Hunion :
      Pr[
        L0.main_with_evidence() @ &m :
          (res.`alae_raw_win \/ res.`alae_authentication_failure) \/
          (res.`alae_raw_win <> res.`alae_authenticated_win /\
           ! res.`alae_authentication_failure)
      ] <=
      Pr[L0.main_with_evidence() @ &m : res.`alae_raw_win] +
      Pr[L0.main_with_evidence() @ &m : res.`alae_authentication_failure] +
      Pr[
        L0.main_with_evidence() @ &m :
          res.`alae_raw_win <> res.`alae_authenticated_win /\
          ! res.`alae_authentication_failure
      ].
    + rewrite !mu_or.
      smt(ge0_mu).

    rewrite authoritative_live_raw_authenticated_difference_zero in Hunion.
    smt().
  qed.

  lemma authoritative_live_advantage_le_authenticated_plus_authloss
      &m :
    authoritative_live_normalized_advantage
      (Pr[L0.main_with_evidence() @ &m : res.`alae_raw_win]) <=
    authoritative_live_normalized_advantage
      (Pr[L0.main_with_evidence() @ &m : res.`alae_authenticated_win]) +
    Pr[
      L0.main_with_evidence() @ &m : res.`alae_authentication_failure
    ].
  proof.
    exact
      (authoritative_live_normalized_advantage_perturbation
         (Pr[L0.main_with_evidence() @ &m : res.`alae_raw_win])
         (Pr[L0.main_with_evidence() @ &m : res.`alae_authenticated_win])
         (Pr[
            L0.main_with_evidence() @ &m :
              res.`alae_authentication_failure
          ])
         (ge0_mu L0.main_with_evidence
            (fun result => result.`alae_authentication_failure) &m)
         (authoritative_live_raw_success_le_authenticated_plus_failure &m)
         (authoritative_live_authenticated_success_le_raw_plus_failure &m)).
  qed.
end section AuthoritativeLiveAuthenticationAdvantage.
