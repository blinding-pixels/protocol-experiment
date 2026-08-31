require import AllCore List FSet.
require import ProtocolTypes ProtocolPrimitives.
require import BeeKemTypes BeeKemProtocol BeeKemKiGame BeeKemConstruction.
require import BeeKemPrimitiveGames BeeKemPrimitiveContracts BeeKemTheorem1Math.
require import LiveKeyGame LivePrfTypes LivePrfGame.
require import LiveAuthenticationReduction LivePrfAuthoritativeReduction.
require import LivePrfAuthoritativeProof.
require import LiveBeeKemAuthoritativeLiveTypes.
require import LiveBeeKemAuthoritativeReduction.
require import LiveBeeKemAuthoritativeHop.
require import LiveBeeKemAuthoritativePrimitiveBound.

(* L2--L3 composition for the authoritative application execution.  The
   random-root BeeKEM branch and the real-PRF application branch are the same
   program after unfolding the two adapters.  The final theorem combines that
   exact H1 identity, the imported BeeKEM primitive theorem, and the concrete
   multi-domain PRF fixed-bit game by ordinary absolute-distance triangle
   algebra. *)
section AuthoritativeLiveBeeKemPrfComposition.
  declare module A <: AUTHORITATIVE_LIVE_KEY_ADVERSARY.
  declare module S <: SIGNATURE_SCHEME.
  declare module Hash <: NODE_HASH.
  declare module K <: MULTI_DOMAIN_KEY_SCHEDULE.
  declare module R <: LIVE_KEY_SAMPLER.
  declare module I <: BEEKEM_PAPER_INSTANCE.

  module LiveBeeKem =
    AuthoritativeLiveBeeKemGame(A, S, Hash, K, R, I).
  module Direct =
    AuthoritativePrfApplicationBit(A, S, Hash, K, R, I).
  module Prf = MultiDomainPrfGame(
    BPRFLiveAuthoritative(A, S, Hash, I), K, R
  ).
  module NikeSymmetry =
    BeeKemNikeSymmetryGame(BeeKemNikeOfPaperInstance(I)).
  module SeCorrectness =
    BeeKemSeCorrectnessGame(BeeKemSeOfPaperInstance(I)).

  lemma authoritative_beekem_random_projection_exactly_direct_prf_real
      &m :
    Pr[
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
    ] =
    Pr[
      Direct.main(
        live_auth_initial_state,
        live_auth_initial_facts,
        live_auth_retention_kappa,
        true
      ) @ &m :
        res.`mpar_eligible /\ res.`mpar_guess
    ].
  proof.
    byequiv
      (_ : ={glob A, glob S, glob Hash, glob K, glob R, glob I}
           ==>
           (res{1}.`bke_safe /\
            ! res{1}.`bke_protocol_consistency_failure /\
            res{1}.`bke_adversary_guess) =
           (res{2}.`mpar_eligible /\ res{2}.`mpar_guess)) => //.
    proc.
    inline LiveBeeKem.main_with_fixed_bit LiveBeeKem.A.attack Direct.main.
    sim.
  qed.

  lemma authoritative_beekem_random_projection_exactly_prf_game_real
      &m :
    Pr[
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
    ] =
    Pr[
      Prf.main_with_fixed_bit(
        live_auth_initial_state,
        live_auth_initial_facts,
        live_auth_retention_kappa,
        true
      ) @ &m :
        res.`mpge_eligible /\ res.`mpge_guess
    ].
  proof.
    rewrite
      authoritative_beekem_random_projection_exactly_direct_prf_real
      (authoritative_application_fixed_bit_one_event_exactly_prf
         A S Hash K R I &m
         live_auth_initial_state
         live_auth_initial_facts
         live_auth_retention_kappa
         true).
    by done.
  qed.

  lemma authoritative_live_beekem_prf_composed_bound
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
              Prf.main_with_fixed_bit(
                live_auth_initial_state,
                live_auth_initial_facts,
                live_auth_retention_kappa,
                false
              ) @ &m :
                res.`mpge_eligible /\ res.`mpge_guess
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
                  ]))
            +
            mdprf_fixed_bit_advantage
              (Pr[
                 Prf.main_with_fixed_bit(
                   live_auth_initial_state,
                   live_auth_initial_facts,
                   live_auth_retention_kappa,
                   true
                 ) @ &m :
                   res.`mpge_eligible /\ res.`mpge_guess
               ])
              (Pr[
                 Prf.main_with_fixed_bit(
                   live_auth_initial_state,
                   live_auth_initial_facts,
                   live_auth_retention_kappa,
                   false
                 ) @ &m :
                   res.`mpge_eligible /\ res.`mpge_guess
               ]) / 2%r.
  proof.
    move=> Hkappa Hchallenge Hheight Hnike Hse Hsafe Hcounters Hconsistent.
    have Hprimitive :=
      authoritative_projected_beekem_advantage_bound
        A S Hash K R I &m
        challenge_bound member_bound logarithmic_height
        Hkappa Hchallenge Hheight Hnike Hse Hsafe Hcounters Hconsistent.
    elim Hprimitive => BNike BSe Hprimitive.
    exists BNike.
    exists BSe.

    have Htriangle :=
      mdprf_fixed_bit_normalized_triangle
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
         ])
        (Pr[
           Prf.main_with_fixed_bit(
             live_auth_initial_state,
             live_auth_initial_facts,
             live_auth_retention_kappa,
             false
           ) @ &m :
             res.`mpge_eligible /\ res.`mpge_guess
         ]).
    rewrite
      (authoritative_beekem_random_projection_exactly_prf_game_real &m)
      in Htriangle.
    smt().
  qed.
end section AuthoritativeLiveBeeKemPrfComposition.
