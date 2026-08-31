require import AllCore List FSet.
require import ProtocolTypes ProtocolPrimitives.
require import BeeKemTypes BeeKemProtocol BeeKemKiGame BeeKemConstruction.
require import BeeKemPrimitiveGames BeeKemPrimitiveContracts BeeKemTheorem1Math.
require import BeeKemProjectedNormalization.
require import LiveKeyGame LivePrfGame.
require import LiveAuthenticationReduction LivePrfAuthoritativeReduction.
require import LiveBeeKemAuthoritativeLiveTypes.
require import LiveBeeKemAuthoritativeReduction.

(* Concrete application projection of the imported BeeKEM Theorem 1.  The
   theorem below keeps every source-theorem side condition explicit: finite
   retention, exact challenge/addition counters, primitive correctness,
   challenger-computed bee-safe_kappa mass, and the implementation-consistency
   boundary for the paper instance.  Its conclusion names the actual
   application-derived BBeeLive adversary and the concrete primitive games. *)
section AuthoritativeLiveBeeKemPrimitiveBound.
  declare module A <: AUTHORITATIVE_LIVE_KEY_ADVERSARY.
  declare module S <: SIGNATURE_SCHEME.
  declare module Hash <: NODE_HASH.
  declare module K <: MULTI_DOMAIN_KEY_SCHEDULE.
  declare module R <: LIVE_KEY_SAMPLER.
  declare module I <: BEEKEM_PAPER_INSTANCE.

  module LiveBeeKem =
    AuthoritativeLiveBeeKemGame(A, S, Hash, K, R, I).
  module NikeSymmetry =
    BeeKemNikeSymmetryGame(BeeKemNikeOfPaperInstance(I)).
  module SeCorrectness =
    BeeKemSeCorrectnessGame(BeeKemSeOfPaperInstance(I)).

  lemma authoritative_projected_beekem_advantage_bound
      &m
      (challenge_bound member_bound logarithmic_height : int) :
       1 <= live_auth_retention_kappa
    => 0 <= challenge_bound
    => beekem_is_ceil_log2 member_bound logarithmic_height
    => Pr[NikeSymmetry.main() @ &m : res] = 1%r
    => (forall message,
         Pr[SeCorrectness.main(message) @ &m : res] = 1%r)
    => Pr[
         LiveBeeKem.main_with_evidence(
           authoritative_live_initial_users,
           authoritative_live_initial_group,
           live_auth_retention_kappa,
           authoritative_live_initial_membership
         ) @ &m : res.`bke_safe
       ] = 1%r
    => Pr[
         LiveBeeKem.main_with_evidence(
           authoritative_live_initial_users,
           authoritative_live_initial_group,
           live_auth_retention_kappa,
           authoritative_live_initial_membership
         ) @ &m :
           res.`bke_challenge_count <= challenge_bound /\
           res.`bke_member_addition_count <= member_bound
       ] = 1%r
    => Pr[
         LiveBeeKem.main_with_fixed_bit(
           authoritative_live_initial_users,
           authoritative_live_initial_group,
           live_auth_retention_kappa,
           authoritative_live_initial_membership,
           true
         ) @ &m : ! res.`bke_protocol_consistency_failure
       ] = 1%r
    => exists (BNike <: BEEKEM_HKR_CKS_ADVERSARY),
       exists (BSe <: BEEKEM_MU_CPA_ADVERSARY),
         mdprf_fixed_bit_advantage
           (Pr[
              LiveBeeKem.main_with_fixed_bit(
                authoritative_live_initial_users,
                authoritative_live_initial_group,
                live_auth_retention_kappa,
                authoritative_live_initial_membership,
                true
              ) @ &m :
                res.`bke_safe /\
                ! res.`bke_protocol_consistency_failure /\
                res.`bke_adversary_guess
            ])
           (Pr[
              LiveBeeKem.main_with_fixed_bit(
                authoritative_live_initial_users,
                authoritative_live_initial_group,
                live_auth_retention_kappa,
                authoritative_live_initial_membership,
                false
              ) @ &m :
                res.`bke_safe /\
                ! res.`bke_protocol_consistency_failure /\
                res.`bke_adversary_guess
            ]) / 2%r
         <= beekem_theorem1_loss challenge_bound logarithmic_height *
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
                ])).
  proof.
    move=> Hkappa Hchallenge Hheight Hnike Hse Hsafe Hcounters Hconsistent.
    have Hprojection :=
      beekem_projected_fixed_bit_advantage_from_sampled_safe_and_consistency
        (BBeeLive(A, S, Hash, K, R))
        (BeeKemProtocolOfPaperInstance(I))
        &m
        authoritative_live_initial_users
        authoritative_live_initial_group
        live_auth_retention_kappa
        authoritative_live_initial_membership
        Hsafe Hconsistent.
    rewrite Hprojection.
    exact
      (authoritative_live_beekem_theorem1
         A S Hash K R I &m
         challenge_bound member_bound logarithmic_height
         Hkappa Hchallenge Hheight Hnike Hse Hsafe Hcounters).
  qed.
end section AuthoritativeLiveBeeKemPrimitiveBound.
