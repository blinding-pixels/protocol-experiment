require import AllCore List FSet Distr.
require import ProtocolTypes ProtocolPrimitives.
require import BeeKemTypes BeeKemProtocol BeeKemKiGame BeeKemConstruction.
require import BeeKemPrimitiveGames BeeKemPrimitiveContracts BeeKemTheorem1Math.
require import BeeKemSafetyBranchProjection.
require import BeeKemConsistencyBranchProjection.
require import LiveKeyGame LivePrfGame.
require import LiveAuthenticationReduction.
require import LivePrfAuthoritativeReduction.
require import LiveBeeKemAuthoritativeAuthentication.
require import LiveBeeKemAuthoritativeAuthenticationBound.
require import LiveBeeKemAuthoritativeSampledReduction.
require import LiveBeeKemAuthoritativeSampledHop.
require import LiveBeeKemAuthoritativeSampledNormalization.
require import LiveBeeKemAuthoritativeSampledComposition.

(* The complete authenticated L0--L4 computational hop for one concrete
   application-derived BeeKEM adversary.  The outer BeeKEM bit changes only the
   group root; the inner fair application bit and every live/history oracle
   remain shared.  Consequently one pair of BeeKEM primitive reductions pays
   for the root hop, while the concrete multi-domain PRF game pays for the
   application-key hop. *)
section AuthoritativeSampledAuthenticatedBound.
  declare module A <: AUTHORITATIVE_LIVE_KEY_ADVERSARY.
  declare module S <: SIGNATURE_SCHEME.
  declare module Hash <: NODE_HASH.
  declare module K <: MULTI_DOMAIN_KEY_SCHEDULE.
  declare module R <: LIVE_KEY_SAMPLER.
  declare module I <: BEEKEM_PAPER_INSTANCE.

  module L0 = AuthoritativeLiveRealGame(A, S, Hash, K, R, I).
  module Bee =
    AuthoritativeSampledLiveBeeKemGame(A, S, Hash, K, R, I).
  module Prf = MultiDomainPrfGame(
    BPRFLiveAuthoritative(A, S, Hash, I), K, R
  ).
  module NikeSymmetry =
    BeeKemNikeSymmetryGame(BeeKemNikeOfPaperInstance(I)).
  module SeCorrectness =
    BeeKemSeCorrectnessGame(BeeKemSeOfPaperInstance(I)).

  lemma authoritative_sampled_authenticated_beekem_prf_bound
      &m
      (challenge_bound member_bound logarithmic_height : int) :
       1 <= live_auth_retention_kappa
    => 0 <= challenge_bound
    => beekem_is_ceil_log2 member_bound logarithmic_height
    => Pr[NikeSymmetry.main() @ &m : res] = 1%r
    => (forall message,
         Pr[SeCorrectness.main(message) @ &m : res] = 1%r)
    => Pr[
         Bee.main_with_evidence(
           authoritative_live_initial_users,
           authoritative_live_initial_group,
           live_auth_retention_kappa,
           authoritative_live_initial_membership
         ) @ &m : res.`bke_safe
       ] = 1%r
    => Pr[
         Bee.main_with_evidence(
           authoritative_live_initial_users,
           authoritative_live_initial_group,
           live_auth_retention_kappa,
           authoritative_live_initial_membership
         ) @ &m :
           res.`bke_challenge_count <= challenge_bound /\
           res.`bke_member_addition_count <= member_bound
       ] = 1%r
    => Pr[
         Bee.main_with_fixed_bit(
           authoritative_live_initial_users,
           authoritative_live_initial_group,
           live_auth_retention_kappa,
           authoritative_live_initial_membership,
           true
         ) @ &m : ! res.`bke_protocol_consistency_failure
       ] = 1%r
    => Pr[
         Bee.main_with_fixed_bit(
           authoritative_live_initial_users,
           authoritative_live_initial_group,
           live_auth_retention_kappa,
           authoritative_live_initial_membership,
           false
         ) @ &m : ! res.`bke_protocol_consistency_failure
       ] = 1%r
    => exists (BNike <: BEEKEM_HKR_CKS_ADVERSARY),
       exists (BSe <: BEEKEM_MU_CPA_ADVERSARY),
         authoritative_live_normalized_advantage
           (Pr[
              L0.main_with_root_evidence(true) @ &m :
                res.`alae_authenticated_win
            ])
         <=
         2%r *
           (beekem_theorem1_loss challenge_bound logarithmic_height *
              (beekem_hkr_cks_advantage
                 (Pr[
                    BeeKemHkrCksGame(
                      BNike,
                      BeeKemNikeOfPaperInstance(I),
                      BeeKemNikeSamplerOfPaperInstance(I)
                    ).main() @ &m : res
                  ]) +
               beekem_mu_cpa_advantage
                 (Pr[
                    BeeKemMuCpaGame(
                      BSe,
                      BeeKemSeOfPaperInstance(I)
                    ).main() @ &m : res
                  ])))
         +
         mdprf_fixed_bit_advantage
           (Pr[
              Prf.main_with_fixed_bit(
                live_auth_initial_state,
                live_auth_initial_facts,
                live_auth_retention_kappa,
                true
              ) @ &m : res.`mpge_eligible /\ res.`mpge_guess
            ])
           (Pr[
              Prf.main_with_fixed_bit(
                live_auth_initial_state,
                live_auth_initial_facts,
                live_auth_retention_kappa,
                false
              ) @ &m : res.`mpge_eligible /\ res.`mpge_guess
            ]) / 2%r.
  proof.
    move=> Hkappa Hchallenge Hheight Hnike Hse Hsafe Hcounters.
    move=> Hconsistent_true Hconsistent_false.

    have Hprimitive :=
      authoritative_sampled_live_beekem_theorem1
        A S Hash K R I &m
        challenge_bound member_bound logarithmic_height
        Hkappa Hchallenge Hheight Hnike Hse Hsafe Hcounters.
    elim Hprimitive => BNike BSe Hprimitive.
    exists BNike.
    exists BSe.

    have Hroot :=
      authoritative_sampled_root_hop_exactly_beekem
        A S Hash K R I &m
        Hsafe Hconsistent_true Hconsistent_false.

    have Hfixed_safe :=
      beekem_sampled_safe_one_implies_fixed_safe_one
        (BBeeLiveSampledApplication(A, S, Hash, K, R))
        (BeeKemProtocolOfPaperInstance(I))
        &m
        authoritative_live_initial_users
        authoritative_live_initial_group
        live_auth_retention_kappa
        authoritative_live_initial_membership
        Hsafe.
    elim Hfixed_safe => Hsafe_true Hsafe_false.

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
           (BBeeLiveSampledApplication(A, S, Hash, K, R))
           (BeeKemProtocolOfPaperInstance(I))
           &m
           authoritative_live_initial_users
           authoritative_live_initial_group
           live_auth_retention_kappa
           authoritative_live_initial_membership
           false Hsafe_false Hconsistent_false).

    have HL0_good_false :
      Pr[
        L0.main_with_root_evidence(false) @ &m :
          res.`alae_beekem_safe /\ ! res.`alae_protocol_failure
      ] = 1%r.
    + rewrite
        (authoritative_sampled_root_good_exact
           A S Hash K R I &m false).
      exact Hgood_false.

    have Hprf :=
      authoritative_random_root_sampled_advantage_exactly_prf
        A S Hash K R I &m HL0_good_false.

    have Htriangle :=
      authoritative_live_centered_triangle
        (Pr[
           L0.main_with_root_evidence(true) @ &m :
             res.`alae_authenticated_win
         ])
        (Pr[
           L0.main_with_root_evidence(false) @ &m :
             res.`alae_authenticated_win
         ]).

    rewrite Hroot Hprf in Htriangle.
    smt().
  qed.
end section AuthoritativeSampledAuthenticatedBound.
