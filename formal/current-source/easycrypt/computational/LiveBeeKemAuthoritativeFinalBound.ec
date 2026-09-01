require import AllCore List FSet Distr.
require import ProtocolTypes ProtocolPrimitives.
require import UnauthorizedSignatureReduction UnauthorizedOriginGame.
require import UnauthorizedOriginFinalBound.
require import OriginOperationDirectInvariant OriginFactWitnessGame.
require import UnauthorizedOriginHashReduction.
require import LiveKeyGame LivePrfGame.
require import LiveAuthenticationReduction.
require import BeeKemTypes BeeKemProtocol BeeKemKiGame BeeKemConstruction.
require import BeeKemPrimitiveGames BeeKemPrimitiveContracts BeeKemTheorem1Math.
require import LivePrfAuthoritativeReduction.
require import LiveBeeKemAuthoritativeLiveTypes.
require import LiveBeeKemAuthoritativeAuthentication.
require import LiveBeeKemAuthoritativeAuthenticationBound.
require import LiveBeeKemAuthoritativeSampledReduction.
require import LiveBeeKemAuthoritativeSampledBound.
require import LiveBeeKemAuthoritativeEntryBridge.

import PG.

(* Keep the final composition independent of every game-specific side
   condition.  This arithmetic lemma can see only the three reduction
   inequalities that are meant to justify the public bound.  In particular,
   contradictory safety, counter, or consistency premises cannot make a
   missing authentication or cryptographic term disappear through explosion. *)
lemma authoritative_live_final_bound_arithmetic
    (raw authenticated failure operation_signature fact_signature
     collision encoding beekem prf : real) :
  raw <= authenticated + failure =>
  failure <=
    operation_signature + fact_signature + collision + encoding =>
  authenticated <= beekem + prf =>
  raw <=
    operation_signature + fact_signature + collision + encoding + beekem + prf.
proof. smt(). qed.

(* Public L0 theorem with every authentication and key-indistinguishability
   loss exposed as its concrete primitive experiment.  The only non-kernel
   assumption is the single imported BeeKEM Theorem 1 boundary already listed
   in the manifest; this theorem merely instantiates and composes it. *)
section AuthoritativeLiveFinalBound.
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

  module EUFOP = PG.MultiUserEUFCMAGame(
    BSignOriginOperationDirect(
      BAuthoritativeLiveOriginAdversary(A, K, R, I), Hash
    ), S
  ).
  module EUFFACT = PG.MultiUserEUFCMAGame(
    BSignOriginFactWitness(
      BAuthoritativeLiveOriginAdversary(A, K, R, I), Hash
    ), S
  ).
  module COLL = PG.NodeCollisionGame(
    BHashOrigin(
      BAuthoritativeLiveOriginAdversary(A, K, R, I), S
    ), Hash
  ).

  lemma authoritative_live_key_l0_l4_bound
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
           (Pr[L0.main() @ &m : res])
         <=
           q_operation_signature_factor *
             Pr[EUFOP.main(live_auth_initial_state) @ &m : res]
         + q_fact_signature_factor *
             Pr[EUFFACT.main(live_auth_initial_state) @ &m : res]
         + Pr[COLL.main(live_auth_initial_state) @ &m : res]
         + encoding_failure_probability
         + 2%r *
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
         + mdprf_fixed_bit_advantage
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

    have Hcrypto :=
      authoritative_sampled_authenticated_beekem_prf_bound
        A S Hash K R I &m
        challenge_bound member_bound logarithmic_height
        Hkappa Hchallenge Hheight Hnike Hse Hsafe Hcounters
        Hconsistent_true Hconsistent_false.
    elim Hcrypto => BNike BSe Hcrypto.
    exists BNike.
    exists BSe.

    have Hauth :=
      authoritative_live_advantage_le_authenticated_plus_authloss
        A S Hash K R I &m.
    have Hauthloss :=
      authoritative_live_authentication_failure_bound
        A S Hash K R I &m.
    have Hauthbridge :=
      authoritative_live_evidence_authenticated_exactly_real_root
        A S Hash K R I &m.
    have Hrawbridge :=
      authoritative_live_public_raw_exactly_evidence
        A S Hash K R I &m.

    rewrite Hauthbridge -Hrawbridge in Hauth.
    exact
      (authoritative_live_final_bound_arithmetic
         (authoritative_live_normalized_advantage
            (Pr[L0.main() @ &m : res]))
         (authoritative_live_normalized_advantage
            (Pr[
               L0.main_with_root_evidence(true) @ &m :
                 res.`alae_authenticated_win
             ]))
         (Pr[
            L0.main_with_evidence() @ &m :
              res.`alae_authentication_failure
          ])
         (q_operation_signature_factor *
            Pr[EUFOP.main(live_auth_initial_state) @ &m : res])
         (q_fact_signature_factor *
            Pr[EUFFACT.main(live_auth_initial_state) @ &m : res])
         (Pr[COLL.main(live_auth_initial_state) @ &m : res])
         encoding_failure_probability
         (2%r *
            (beekem_theorem1_loss
               challenge_bound logarithmic_height *
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
                   ]))))
         (mdprf_fixed_bit_advantage
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
             ]) / 2%r)
         Hauth Hauthloss Hcrypto).
  qed.
end section AuthoritativeLiveFinalBound.
