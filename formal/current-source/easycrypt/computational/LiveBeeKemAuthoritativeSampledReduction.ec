require import AllCore List FSet Distr DBool.
require import ProtocolTypes ProtocolPrimitives AuthorizationState.
require import UnauthorizedSignatureReduction UnauthorizedOriginGame.
require import LiveKeyGame LiveAuthenticationReduction.
require import BeeKemTypes BeeKemProtocol BeeKemKiGame BeeKemConstruction.
require import BeeKemPrimitiveGames BeeKemPrimitiveContracts BeeKemTheorem1Math.
require BeeKemKiInterface.
clone import BeeKemKiInterface as BKI.
require import LiveBeeKemAuthoritativeTypes.
require import LiveBeeKemAuthoritativeLiveTypes.
require import LiveBeeKemAuthoritativeLiveOracle.
require import LivePrfGame LivePrfApplicationReduction.
require import LivePrfAuthoritativeAdapter.
require import LivePrfAuthoritativeReduction.

import PG.

(* One BeeKEM adversary represents the complete sampled application hidden-bit
   game.  It samples the application bit internally, routes the distinguished
   accepted live challenge through that exact PRF branch, and returns whether
   the resulting application decision guessed the application bit.  The outer
   KI-DCGKA bit therefore changes only the BeeKEM root while preserving one
   shared application experiment, so Theorem 1 yields one pair of primitive
   reductions rather than two unrelated branch-specific pairs. *)
module BBeeLiveSampledApplication(
  A : AUTHORITATIVE_LIVE_KEY_ADVERSARY,
  S : SIGNATURE_SCHEME,
  H : NODE_HASH,
  K : MULTI_DOMAIN_KEY_SCHEDULE,
  R : LIVE_KEY_SAMPLER
)(O : BEEKEM_KI_ORACLES) = {
  module SO = PG.LoggedSignatureOracle(S)
  module Auth = OriginTrackedCandidateEnvironment(SO, H)
  module Prf = MultiDomainPrfOracle(K, R)
  module Routed = PrfOracleBackedKeySchedule(Prf)
  module Core = AuthoritativeLiveProtocolOracle(Auth, O, Routed)
  module Live = AuthoritativePrfBackedLiveOracle(Core, Routed)
  module A = A(Live)

  var application_bit : bool
  var initial_authorization_valid : bool
  var application_challenge_count : int
  var authentication_failure : bool
  var adapter_fault : bool
  var adversary_guess : bool
  var application_decision : bool
  var application_win : bool

  proc attack() : bool = {
    SO.init();
    Auth.init(live_auth_initial_state);
    application_bit <$ dbool;
    Prf.init(application_bit);
    Routed.init();
    Core.init(
      authoritative_live_initial_registry,
      live_auth_initial_state,
      live_auth_initial_digest
    );

    A.attack();
    adversary_guess <@ A.guess();

    initial_authorization_valid <-
      live_auth_initial_authorization <> None;
    application_challenge_count <-
      challenge_query_count Core.derived_queries;
    authentication_failure <- Auth.unauthorized_accepted;
    adapter_fault <- Core.runtime_fault;
    application_decision <-
         initial_authorization_valid
      /\ 0 < application_challenge_count
      /\ ! authentication_failure
      /\ ! adapter_fault
      /\ adversary_guess;
    application_win <- application_decision = application_bit;
    return application_win;
  }
}.

module AuthoritativeSampledLiveBeeKemGame(
  A : AUTHORITATIVE_LIVE_KEY_ADVERSARY,
  S : SIGNATURE_SCHEME,
  H : NODE_HASH,
  K : MULTI_DOMAIN_KEY_SCHEDULE,
  R : LIVE_KEY_SAMPLER,
  I : BEEKEM_PAPER_INSTANCE
) =
  BeeKemKiGame(
    BBeeLiveSampledApplication(A, S, H, K, R),
    BeeKemProtocolOfPaperInstance(I)
  ).

section AuthoritativeSampledLiveBeeKemTheorem.
  declare module A <: AUTHORITATIVE_LIVE_KEY_ADVERSARY.
  declare module S <: SIGNATURE_SCHEME.
  declare module Hash <: NODE_HASH.
  declare module K <: MULTI_DOMAIN_KEY_SCHEDULE.
  declare module R <: LIVE_KEY_SAMPLER.
  declare module I <: BEEKEM_PAPER_INSTANCE.

  module SampledBeeKem =
    AuthoritativeSampledLiveBeeKemGame(A, S, Hash, K, R, I).
  module NikeSymmetry =
    BeeKemNikeSymmetryGame(BeeKemNikeOfPaperInstance(I)).
  module SeCorrectness =
    BeeKemSeCorrectnessGame(BeeKemSeOfPaperInstance(I)).

  lemma authoritative_sampled_live_beekem_theorem1
      &m
      (challenge_bound member_bound logarithmic_height : int) :
       1 <= live_auth_retention_kappa
    => 0 <= challenge_bound
    => beekem_is_ceil_log2 member_bound logarithmic_height
    => Pr[NikeSymmetry.main() @ &m : res] = 1%r
    => (forall message,
         Pr[SeCorrectness.main(message) @ &m : res] = 1%r)
    => Pr[
         SampledBeeKem.main_with_evidence(
           authoritative_live_initial_users,
           authoritative_live_initial_group,
           live_auth_retention_kappa,
           authoritative_live_initial_membership
         ) @ &m : res.`bke_safe
       ] = 1%r
    => Pr[
         SampledBeeKem.main_with_evidence(
           authoritative_live_initial_users,
           authoritative_live_initial_group,
           live_auth_retention_kappa,
           authoritative_live_initial_membership
         ) @ &m :
           res.`bke_challenge_count <= challenge_bound /\
           res.`bke_member_addition_count <= member_bound
       ] = 1%r
    => exists (BNike <: BEEKEM_HKR_CKS_ADVERSARY),
       exists (BSe <: BEEKEM_MU_CPA_ADVERSARY),
         beekem_normalized_ki_advantage
           (Pr[
              SampledBeeKem.main(
                authoritative_live_initial_users,
                authoritative_live_initial_group,
                live_auth_retention_kappa,
                authoritative_live_initial_membership
              ) @ &m : res
            ])
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
    exact
      (BKI.beekem_theorem1_imported_normalized
         (BBeeLiveSampledApplication(A, S, Hash, K, R)) I &m
         authoritative_live_initial_users
         authoritative_live_initial_group
         live_auth_retention_kappa
         challenge_bound member_bound logarithmic_height
         authoritative_live_initial_membership).
  qed.
end section AuthoritativeSampledLiveBeeKemTheorem.
