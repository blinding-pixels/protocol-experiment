require import AllCore List FSet.
require import ProtocolTypes ProtocolPrimitives AuthorizationState.
require import UnauthorizedSignatureReduction UnauthorizedOriginGame.
require import LiveKeyGame LiveAuthenticationReduction.
require import BeeKemTypes BeeKemProtocol BeeKemKiGame BeeKemConstruction.
require import LiveBeeKemAuthoritativeTypes.
require import LiveBeeKemAuthoritativeLiveTypes.
require import LiveBeeKemAuthoritativeLiveOracle.
require import LivePrfAuthoritativeAdapter.

import PG.

(* Application configuration carried into the concrete BeeKEM reduction.
   These are ordinary universally interpreted game inputs, not security
   assumptions.  The exact Figure-8 challenger still owns BeeKEM initialization,
   hidden-bit sampling, the complete query log, safety, and counters. *)
op authoritative_live_initial_registry : application_user_registry.
op authoritative_live_initial_users : beekem_user list.
op authoritative_live_initial_membership : beekem_dgm.

op authoritative_live_initial_group : beekem_group =
  application_group_of_document live_auth_initial_state.`ps_document_id.

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
