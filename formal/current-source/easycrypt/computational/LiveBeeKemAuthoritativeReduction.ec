require import AllCore List FSet.
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
require import LivePrfAuthoritativeAdapter.
require import LivePrfAuthoritativeReduction.
require import LivePrfAuthoritativeProof.

import PG.

(* Concrete application adversary for the authoritative KI-DCGKA game.  The
   wrapper exposes the complete application surface, including production
   authorization, create/add/remove/update/deliver, reveal, challenge, history
   disclosures, and full member-state compromise.  It never samples or returns
   a BeeKEM root: every application challenge reaches [O.challenge] through
   [AuthoritativeLiveProtocolOracle].

   The real application schedule mirrors the exact primitive PRF call trace:
   ordinary live reveals and both history domains are real-only, while the
   distinguished application challenge evaluates the real KDF and one unused
   sampler call.  Thus the BeeKEM hybrid and the PRF-real endpoint can later be
   related by exact program equivalence rather than a transcript premise.

   Authentication failure and adapter inconsistency are computed from the
   shared execution and filter the reduction guess.  They are not supplied by
   the adversary.  Deliverable A charges the former separately; the latter is
   an explicit implementation-faithfulness boundary. *)
module BBeeLive(
  A : AUTHORITATIVE_LIVE_KEY_ADVERSARY,
  S : SIGNATURE_SCHEME,
  H : NODE_HASH,
  K : MULTI_DOMAIN_KEY_SCHEDULE,
  R : LIVE_KEY_SAMPLER
)(O : BEEKEM_KI_ORACLES) = {
  module SO = PG.LoggedSignatureOracle(S)
  module Auth = OriginTrackedCandidateEnvironment(SO, H)
  module KReal = RealChallengeKeySchedule(K, R)
  module Core = AuthoritativeLiveProtocolOracle(Auth, O, KReal)
  module Live = AuthoritativePrfBackedLiveOracle(Core, KReal)
  module A = A(Live)

  var initial_authorization_valid : bool
  var authentication_failure : bool
  var adapter_fault : bool
  var adversary_guess : bool
  var reduction_guess : bool

  proc attack() : bool = {
    SO.init();
    Auth.init(live_auth_initial_state);
    KReal.init();
    Core.init(
      authoritative_live_initial_registry,
      live_auth_initial_state,
      live_auth_initial_digest
    );

    A.attack();
    adversary_guess <@ A.guess();

    initial_authorization_valid <-
      live_auth_initial_authorization <> None;
    authentication_failure <- Auth.unauthorized_accepted;
    adapter_fault <- Core.runtime_fault;
    reduction_guess <-
         initial_authorization_valid
      /\ ! authentication_failure
      /\ ! adapter_fault
      /\ adversary_guess;
    return reduction_guess;
  }
}.

(* The protocol and primitive adapters supplied to the imported Theorem 1 all
   come from this same paper instance.  Hence the named application reduction
   cannot silently switch to an unrelated BeeKEM implementation. *)
module AuthoritativeLiveBeeKemGame(
  A : AUTHORITATIVE_LIVE_KEY_ADVERSARY,
  S : SIGNATURE_SCHEME,
  H : NODE_HASH,
  K : MULTI_DOMAIN_KEY_SCHEDULE,
  R : LIVE_KEY_SAMPLER,
  I : BEEKEM_PAPER_INSTANCE
) =
  BeeKemKiGame(
    BBeeLive(A, S, H, K, R),
    BeeKemProtocolOfPaperInstance(I)
  ).

(* Exact specialization of the sole imported BeeKEM theorem to the concrete
   application-derived KI adversary.  The side conditions are the theorem's
   challenger-computed finite-kappa safety event and executable counters; no
   application adversary supplies a safety bit or a query bound. *)
section AuthoritativeLiveBeeKemTheorem.
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

  lemma authoritative_live_beekem_theorem1
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
    => exists (BNike <: BEEKEM_HKR_CKS_ADVERSARY),
       exists (BSe <: BEEKEM_MU_CPA_ADVERSARY),
         beekem_normalized_ki_advantage
           (Pr[
              LiveBeeKem.main(
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
         (BBeeLive(A, S, Hash, K, R)) I &m
         authoritative_live_initial_users
         authoritative_live_initial_group
         live_auth_retention_kappa
         challenge_bound member_bound logarithmic_height
         authoritative_live_initial_membership).
  qed.
end section AuthoritativeLiveBeeKemTheorem.
