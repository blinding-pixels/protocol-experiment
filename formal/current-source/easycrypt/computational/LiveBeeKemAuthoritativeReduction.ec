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
  var application_challenge_count : int
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
    application_challenge_count <-
      challenge_query_count Core.derived_queries;
    authentication_failure <- Auth.unauthorized_accepted;
    adapter_fault <- Core.runtime_fault;
    reduction_guess <-
         initial_authorization_valid
      /\ 0 < application_challenge_count
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

(* Fixed-bit application projection of the authoritative BeeKEM hybrid.  This
   is the direct H0/H1 endpoint: the BeeKEM bit alone changes the challenge
   root, while the live challenge remains on the real multi-domain KDF
   schedule.  Its eligibility is computed from the same canonical graph, log,
   authorization state, adapter fault, and protocol-consistency state as the
   authoritative PRF endpoint. *)
module AuthoritativeBeeKemApplicationBit(
  A : AUTHORITATIVE_LIVE_KEY_ADVERSARY,
  S : SIGNATURE_SCHEME,
  H : NODE_HASH,
  K : MULTI_DOMAIN_KEY_SCHEDULE,
  R : LIVE_KEY_SAMPLER,
  I : BEEKEM_PAPER_INSTANCE
) = {
  module Bee = BeeKemKiOracles(BeeKemProtocolOfPaperInstance(I))
  module SO = PG.LoggedSignatureOracle(S)
  module Auth = OriginTrackedCandidateEnvironment(SO, H)
  module KReal = RealChallengeKeySchedule(K, R)
  module Core = AuthoritativeLiveProtocolOracle(Auth, Bee, KReal)
  module Live = AuthoritativePrfBackedLiveOracle(Core, KReal)
  module A = A(Live)

  proc main(beekem_bit : bool) : mdprf_adversary_result = {
    var initial_authorization_valid : bool;
    var application_challenge_count : int;
    var beekem_safe : bool;
    var authentication_failure : bool;
    var adapter_fault : bool;
    var protocol_failure : bool;
    var adversary_guess : bool;
    var eligible : bool;

    Bee.initialize(
      authoritative_live_initial_users,
      authoritative_live_initial_group,
      live_auth_retention_kappa,
      authoritative_live_initial_membership,
      beekem_bit
    );
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
    application_challenge_count <-
      challenge_query_count Core.derived_queries;
    beekem_safe <- bee_safe_kappa
      live_auth_retention_kappa
      Bee.Environment.state.`bps_operations
      Bee.Environment.query_log;
    authentication_failure <- Auth.unauthorized_accepted;
    adapter_fault <- Core.runtime_fault;
    protocol_failure <- Bee.Environment.protocol_consistency_failure;
    eligible <- authoritative_live_eligible
      initial_authorization_valid
      application_challenge_count
      beekem_safe
      authentication_failure
      adapter_fault
      protocol_failure;

    return
      {| mpar_eligible = eligible;
         mpar_guess = adversary_guess |};
  }
}.

module AuthoritativeLiveBeeKemFixedProjection(
  A : AUTHORITATIVE_LIVE_KEY_ADVERSARY,
  S : SIGNATURE_SCHEME,
  H : NODE_HASH,
  K : MULTI_DOMAIN_KEY_SCHEDULE,
  R : LIVE_KEY_SAMPLER,
  I : BEEKEM_PAPER_INSTANCE
) = {
  module G = AuthoritativeLiveBeeKemGame(A, S, H, K, R, I)

  proc main(beekem_bit : bool) : beekem_ki_evidence = {
    var evidence : beekem_ki_evidence;
    evidence <@ G.main_with_fixed_bit(
      authoritative_live_initial_users,
      authoritative_live_initial_group,
      live_auth_retention_kappa,
      authoritative_live_initial_membership,
      beekem_bit
    );
    return evidence;
  }
}.

module AuthoritativePrfRealProjection(
  A : AUTHORITATIVE_LIVE_KEY_ADVERSARY,
  S : SIGNATURE_SCHEME,
  H : NODE_HASH,
  K : MULTI_DOMAIN_KEY_SCHEDULE,
  R : LIVE_KEY_SAMPLER,
  I : BEEKEM_PAPER_INSTANCE
) = {
  module G = AuthoritativePrfApplicationBit(A, S, H, K, R, I)

  proc main() : mdprf_adversary_result = {
    var result : mdprf_adversary_result;
    result <@ G.main(
      live_auth_initial_state,
      live_auth_initial_facts,
      live_auth_retention_kappa,
      true
    );
    return result;
  }
}.

module AuthoritativeBeeKemRandomProjection(
  A : AUTHORITATIVE_LIVE_KEY_ADVERSARY,
  S : SIGNATURE_SCHEME,
  H : NODE_HASH,
  K : MULTI_DOMAIN_KEY_SCHEDULE,
  R : LIVE_KEY_SAMPLER,
  I : BEEKEM_PAPER_INSTANCE
) = {
  module G = AuthoritativeBeeKemApplicationBit(A, S, H, K, R, I)

  proc main() : mdprf_adversary_result = {
    var result : mdprf_adversary_result;
    result <@ G.main(false);
    return result;
  }
}.

section AuthoritativeLiveBeeKemEndpointBridge.
  declare module A <: AUTHORITATIVE_LIVE_KEY_ADVERSARY.
  declare module S <: SIGNATURE_SCHEME.
  declare module H <: NODE_HASH.
  declare module K <: MULTI_DOMAIN_KEY_SCHEDULE.
  declare module R <: LIVE_KEY_SAMPLER.
  declare module I <: BEEKEM_PAPER_INSTANCE.

  module Direct = AuthoritativeBeeKemApplicationBit(A, S, H, K, R, I).
  module Fixed = AuthoritativeLiveBeeKemFixedProjection(A, S, H, K, R, I).
  module RandomRoot =
    AuthoritativeBeeKemRandomProjection(A, S, H, K, R, I).
  module PrfReal = AuthoritativePrfRealProjection(A, S, H, K, R, I).

  lemma authoritative_beekem_fixed_bit_one_event_exact
      &m (beekem_bit : bool) :
    Pr[
      Direct.main(beekem_bit) @ &m :
        res.`mpar_eligible /\ res.`mpar_guess
    ] =
    Pr[
      Fixed.main(beekem_bit) @ &m :
        res.`bke_safe /\
        ! res.`bke_protocol_consistency_failure /\
        res.`bke_adversary_guess
    ].
  proof.
    byequiv
      (_ : ={beekem_bit, glob A, glob S, glob H, glob K, glob R, glob I}
           ==>
           (res{1}.`mpar_eligible /\ res{1}.`mpar_guess) =
           (res{2}.`bke_safe /\
            ! res{2}.`bke_protocol_consistency_failure /\
            res{2}.`bke_adversary_guess)) => //.
    proc.
    inline *.
    sim.
  qed.

  (* The H1 endpoint is definitionally the same execution on both sides: the
     BeeKEM challenger supplies its random-root branch and the PRF challenger
     is fixed to its real branch.  Both schedules evaluate K and the unused R
     call in the same order at each accepted live challenge. *)
  lemma authoritative_beekem_random_root_exactly_prf_real &m :
    Pr[
      RandomRoot.main() @ &m :
        res.`mpar_eligible /\ res.`mpar_guess
    ] =
    Pr[
      PrfReal.main() @ &m :
        res.`mpar_eligible /\ res.`mpar_guess
    ].
  proof.
    byequiv
      (_ : ={glob A, glob S, glob H, glob K, glob R, glob I}
           ==>
           (res{1}.`mpar_eligible /\ res{1}.`mpar_guess) =
           (res{2}.`mpar_eligible /\ res{2}.`mpar_guess)) => //.
    proc.
    inline *.
    sim.
  qed.
end section AuthoritativeLiveBeeKemEndpointBridge.

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
