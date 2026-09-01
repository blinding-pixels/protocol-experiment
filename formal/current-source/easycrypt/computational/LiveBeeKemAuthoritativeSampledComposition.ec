require import AllCore List FSet Distr.
require import ProtocolTypes ProtocolPrimitives.
require import BeeKemTypes BeeKemProtocol BeeKemKiGame BeeKemConstruction.
require import BeeKemSafetyBranchProjection.
require import BeeKemConsistencyBranchProjection.
require import BeeKemProjectedNormalization.
require import LiveKeyGame LivePrfGame.
require import LiveAuthenticationReduction.
require import LiveBeeKemAuthoritativeLiveTypes.
require import LiveBeeKemAuthoritativeAuthentication.
require import LiveBeeKemAuthoritativeAuthenticationBound.
require import LiveBeeKemAuthoritativeSampledReduction.
require import LiveBeeKemAuthoritativeSampledHop.
require import LiveBeeKemAuthoritativeSampledNormalization.

(* Center the real-root application success at its fair hidden-bit baseline,
   then insert the random-root application experiment as the intermediate
   distribution.  The factor two is explicit: the BeeKEM game uses centered
   hidden-bit advantage, which is one half of the fixed-root event distance. *)
lemma authoritative_live_centered_triangle
    (real_root_success random_root_success : real) :
  authoritative_live_normalized_advantage real_root_success <=
    2%r *
      (mdprf_fixed_bit_advantage
         real_root_success random_root_success / 2%r) +
    authoritative_live_normalized_advantage random_root_success.
proof.
  rewrite /authoritative_live_normalized_advantage
    /mdprf_normalized_advantage /mdprf_fixed_bit_advantage.
  case (1%r / 2%r <= real_root_success);
  case (random_root_success <= real_root_success);
  case (1%r / 2%r <= random_root_success);
  smt().
qed.

section AuthoritativeSampledRootHop.
  declare module A <: AUTHORITATIVE_LIVE_KEY_ADVERSARY.
  declare module S <: SIGNATURE_SCHEME.
  declare module H <: NODE_HASH.
  declare module K <: MULTI_DOMAIN_KEY_SCHEDULE.
  declare module R <: LIVE_KEY_SAMPLER.
  declare module I <: BEEKEM_PAPER_INSTANCE.

  module L0 = AuthoritativeLiveRealGame(A, S, H, K, R, I).
  module Bee = AuthoritativeSampledLiveBeeKemGame(A, S, H, K, R, I).

  (* Probability-one safety and implementation consistency let us remove the
     explicit good-event filter from the sampled L0 win probability.  This is
     measure algebra only; it does not turn the side condition into a pointwise
     assumption about the adversary. *)
  lemma authoritative_sampled_root_win_probability_is_good_win
      &m (root_bit : bool) :
    Pr[
      L0.main_with_root_evidence(root_bit) @ &m :
        res.`alae_beekem_safe /\ ! res.`alae_protocol_failure
    ] = 1%r =>
    Pr[
      L0.main_with_root_evidence(root_bit) @ &m :
        res.`alae_authenticated_win
    ] =
    Pr[
      L0.main_with_root_evidence(root_bit) @ &m :
        res.`alae_beekem_safe /\
        ! res.`alae_protocol_failure /\
        res.`alae_authenticated_win
    ].
  proof.
    move=> Hgood.

    have Htotal :
      Pr[
        L0.main_with_root_evidence(root_bit) @ &m : true
      ] = 1%r.
    + have Hsub :
        Pr[
          L0.main_with_root_evidence(root_bit) @ &m :
            res.`alae_beekem_safe /\ ! res.`alae_protocol_failure
        ] <=
        Pr[
          L0.main_with_root_evidence(root_bit) @ &m : true
        ].
      * rewrite Pr[mu_sub]=> /#.
      smt(mu_bounded).

    have Hbad_split :
      Pr[
        L0.main_with_root_evidence(root_bit) @ &m : true
      ] =
      Pr[
        L0.main_with_root_evidence(root_bit) @ &m :
          res.`alae_beekem_safe /\ ! res.`alae_protocol_failure
      ] +
      Pr[
        L0.main_with_root_evidence(root_bit) @ &m :
          ! (res.`alae_beekem_safe /\ ! res.`alae_protocol_failure)
      ].
    + by rewrite Pr[mu_split
         (res.`alae_beekem_safe /\ ! res.`alae_protocol_failure)].

    have Hbad_zero :
      Pr[
        L0.main_with_root_evidence(root_bit) @ &m :
          ! (res.`alae_beekem_safe /\ ! res.`alae_protocol_failure)
      ] = 0%r.
    + smt().

    have Hwin_split :
      Pr[
        L0.main_with_root_evidence(root_bit) @ &m :
          res.`alae_authenticated_win
      ] =
      Pr[
        L0.main_with_root_evidence(root_bit) @ &m :
          res.`alae_authenticated_win /\
          (res.`alae_beekem_safe /\ ! res.`alae_protocol_failure)
      ] +
      Pr[
        L0.main_with_root_evidence(root_bit) @ &m :
          res.`alae_authenticated_win /\
          ! (res.`alae_beekem_safe /\ ! res.`alae_protocol_failure)
      ].
    + by rewrite Pr[mu_split
         (res.`alae_beekem_safe /\ ! res.`alae_protocol_failure)].

    have Hbad_win_le :
      Pr[
        L0.main_with_root_evidence(root_bit) @ &m :
          res.`alae_authenticated_win /\
          ! (res.`alae_beekem_safe /\ ! res.`alae_protocol_failure)
      ] <=
      Pr[
        L0.main_with_root_evidence(root_bit) @ &m :
          ! (res.`alae_beekem_safe /\ ! res.`alae_protocol_failure)
      ].
    + rewrite Pr[mu_sub]=> /#.

    have Hbad_win_zero :
      Pr[
        L0.main_with_root_evidence(root_bit) @ &m :
          res.`alae_authenticated_win /\
          ! (res.`alae_beekem_safe /\ ! res.`alae_protocol_failure)
      ] = 0%r.
    + smt(ge0_mu).

    have Hcommute :
      Pr[
        L0.main_with_root_evidence(root_bit) @ &m :
          res.`alae_authenticated_win /\
          (res.`alae_beekem_safe /\ ! res.`alae_protocol_failure)
      ] =
      Pr[
        L0.main_with_root_evidence(root_bit) @ &m :
          res.`alae_beekem_safe /\
          ! res.`alae_protocol_failure /\
          res.`alae_authenticated_win
      ].
    + by rewrite Pr[mu_eq] /#.

    smt().
  qed.

  (* The single sampled application adversary now measures exactly the root
     hop used by L0.  Both fixed-root implementation-consistency obligations
     stay explicit because an adaptive application may react differently to a
     real BeeKEM root and an independently sampled root. *)
  lemma authoritative_sampled_root_hop_exactly_beekem
      &m :
    Pr[
      Bee.main_with_evidence(
        authoritative_live_initial_users,
        authoritative_live_initial_group,
        live_auth_retention_kappa,
        authoritative_live_initial_membership
      ) @ &m : res.`bke_safe
    ] = 1%r =>
    Pr[
      Bee.main_with_fixed_bit(
        authoritative_live_initial_users,
        authoritative_live_initial_group,
        live_auth_retention_kappa,
        authoritative_live_initial_membership,
        true
      ) @ &m : ! res.`bke_protocol_consistency_failure
    ] = 1%r =>
    Pr[
      Bee.main_with_fixed_bit(
        authoritative_live_initial_users,
        authoritative_live_initial_group,
        live_auth_retention_kappa,
        authoritative_live_initial_membership,
        false
      ) @ &m : ! res.`bke_protocol_consistency_failure
    ] = 1%r =>
    mdprf_fixed_bit_advantage
      (Pr[
         L0.main_with_root_evidence(true) @ &m :
           res.`alae_authenticated_win
       ])
      (Pr[
         L0.main_with_root_evidence(false) @ &m :
           res.`alae_authenticated_win
       ]) / 2%r =
    beekem_normalized_ki_advantage
      (Pr[
         Bee.main(
           authoritative_live_initial_users,
           authoritative_live_initial_group,
           live_auth_retention_kappa,
           authoritative_live_initial_membership
         ) @ &m : res
       ]).
  proof.
    move=> Hsafe Hconsistent_true Hconsistent_false.

    have Hfixed_safe :=
      beekem_sampled_safe_one_implies_fixed_safe_one
        (BBeeLiveSampledApplication(A, S, H, K, R))
        (BeeKemProtocolOfPaperInstance(I))
        &m
        authoritative_live_initial_users
        authoritative_live_initial_group
        live_auth_retention_kappa
        authoritative_live_initial_membership
        Hsafe.
    elim Hfixed_safe => Hsafe_true Hsafe_false.

    have Hgood_true :
      Pr[
        Bee.main_with_fixed_bit(
          authoritative_live_initial_users,
          authoritative_live_initial_group,
          live_auth_retention_kappa,
          authoritative_live_initial_membership,
          true
        ) @ &m :
          res.`bke_safe /\ ! res.`bke_protocol_consistency_failure
      ] = 1%r.
    + exact
        (beekem_fixed_safe_and_consistent_probability_one
           (BBeeLiveSampledApplication(A, S, H, K, R))
           (BeeKemProtocolOfPaperInstance(I))
           &m
           authoritative_live_initial_users
           authoritative_live_initial_group
           live_auth_retention_kappa
           authoritative_live_initial_membership
           true Hsafe_true Hconsistent_true).

    have Hgood_false :
      Pr[
        Bee.main_with_fixed_bit(
          authoritative_live_initial_users,
          authoritative_live_initial_group,
          live_auth_retention_kappa,
          authoritative_live_initial_membership,
          false
        ) @ &m :
          res.`bke_safe /\ ! res.`bke_protocol_consistency_failure
      ] = 1%r.
    + exact
        (beekem_fixed_safe_and_consistent_probability_one
           (BBeeLiveSampledApplication(A, S, H, K, R))
           (BeeKemProtocolOfPaperInstance(I))
           &m
           authoritative_live_initial_users
           authoritative_live_initial_group
           live_auth_retention_kappa
           authoritative_live_initial_membership
           false Hsafe_false Hconsistent_false).

    have HL0_good_true :
      Pr[
        L0.main_with_root_evidence(true) @ &m :
          res.`alae_beekem_safe /\ ! res.`alae_protocol_failure
      ] = 1%r.
    + rewrite
        (authoritative_sampled_root_good_exact
           A S H K R I &m true).
      exact Hgood_true.

    have HL0_good_false :
      Pr[
        L0.main_with_root_evidence(false) @ &m :
          res.`alae_beekem_safe /\ ! res.`alae_protocol_failure
      ] = 1%r.
    + rewrite
        (authoritative_sampled_root_good_exact
           A S H K R I &m false).
      exact Hgood_false.

    have Hwin_true :=
      authoritative_sampled_root_win_probability_is_good_win
        &m true HL0_good_true.
    have Hwin_false :=
      authoritative_sampled_root_win_probability_is_good_win
        &m false HL0_good_false.

    have Hprojection :=
      beekem_projected_fixed_bit_advantage_from_sampled_safe_and_consistency
        (BBeeLiveSampledApplication(A, S, H, K, R))
        (BeeKemProtocolOfPaperInstance(I))
        &m
        authoritative_live_initial_users
        authoritative_live_initial_group
        live_auth_retention_kappa
        authoritative_live_initial_membership
        Hsafe Hconsistent_true.

    rewrite
      -(authoritative_sampled_root_projection_exact
          A S H K R I &m true)
      -(authoritative_sampled_root_projection_exact
          A S H K R I &m false)
      -Hwin_true -Hwin_false
      in Hprojection.
    exact Hprojection.
  qed.
end section AuthoritativeSampledRootHop.
