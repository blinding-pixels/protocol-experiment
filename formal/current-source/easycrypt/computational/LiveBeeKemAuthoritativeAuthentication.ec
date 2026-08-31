require import AllCore List FSet Distr DBool.
require import ProtocolTypes CanonicalEncoding ProtocolPrimitives AuthorizationState.
require import UnauthorizedSignatureReduction UnauthorizedOriginGame.
require import UnauthorizedOriginPartition UnauthorizedOriginFinalBound.
require import OriginOperationDirectInvariant OriginFactWitnessGame.
require import OriginFactReductionWitness UnauthorizedOriginHashReduction.
require import LiveKeyGame LiveAuthenticationReduction.
require import BeeKemTypes BeeKemProtocol BeeKemQueryLog BeeKemSafety BeeKemKiGame.
require import BeeKemConstruction.
require import LivePrfTypes LivePrfGame LivePrfApplicationReduction.
require import LiveBeeKemAuthoritativeTypes.
require import LiveBeeKemAuthoritativeLiveTypes.
require import LiveBeeKemAuthoritativeLiveOracle.
require import LivePrfAuthoritativeAdapter LivePrfAuthoritativeReduction.

import PG.

(* Exact L0 execution evidence.  The application challenge bit is independent
   of the BeeKEM challenge bit.  Raw eligibility is computed from the actual
   production authorization state, accepted application challenge log, exact
   BeeKEM safety predicate, adapter state, and protocol-consistency state.
   Authentication filtering removes only Deliverable A's executable
   unauthorized-acceptance event. *)
type authoritative_live_application_evidence = {
  alae_application_bit : bool;
  alae_initial_authorization_valid : bool;
  alae_application_challenge_count : int;
  alae_beekem_safe : bool;
  alae_authentication_failure : bool;
  alae_adapter_fault : bool;
  alae_protocol_failure : bool;
  alae_adversary_guess : bool;
  alae_raw_eligible : bool;
  alae_authenticated_eligible : bool;
  alae_raw_decision : bool;
  alae_authenticated_decision : bool;
  alae_raw_win : bool;
  alae_authenticated_win : bool
}.

op authoritative_live_raw_eligible
    (initial_authorization_valid : bool)
    (application_challenge_count : int)
    (beekem_safe : bool)
    (adapter_fault : bool)
    (protocol_failure : bool) : bool =
     initial_authorization_valid
  /\ 0 < application_challenge_count
  /\ beekem_safe
  /\ ! adapter_fault
  /\ ! protocol_failure.

op authoritative_live_authenticated_eligible
    (initial_authorization_valid : bool)
    (application_challenge_count : int)
    (beekem_safe : bool)
    (authentication_failure : bool)
    (adapter_fault : bool)
    (protocol_failure : bool) : bool =
  authoritative_live_raw_eligible
    initial_authorization_valid
    application_challenge_count
    beekem_safe
    adapter_fault
    protocol_failure
  /\ ! authentication_failure.

lemma authoritative_live_authenticated_implies_raw
    (initial_authorization_valid : bool)
    (application_challenge_count : int)
    (beekem_safe : bool)
    (authentication_failure : bool)
    (adapter_fault : bool)
    (protocol_failure : bool) :
  authoritative_live_authenticated_eligible
    initial_authorization_valid
    application_challenge_count
    beekem_safe
    authentication_failure
    adapter_fault
    protocol_failure =>
  authoritative_live_raw_eligible
    initial_authorization_valid
    application_challenge_count
    beekem_safe
    adapter_fault
    protocol_failure.
proof.
  by rewrite /authoritative_live_authenticated_eligible.
qed.

(* One shared execution kernel is used by the public L0 game and by the exact
   Deliverable A reduction adversary below.  The supplied authentication oracle
   is the only source of signing and validation.  The BeeKEM root bit is fixed
   separately from the application challenge bit, and every derived domain is
   routed through the actual multi-domain PRF oracle. *)
module AuthoritativeLiveApplicationExecution(
  A : AUTHORITATIVE_LIVE_KEY_ADVERSARY,
  K : MULTI_DOMAIN_KEY_SCHEDULE,
  R : LIVE_KEY_SAMPLER,
  I : BEEKEM_PAPER_INSTANCE
)(Auth : ORIGIN_TRACKED_UNAUTHORIZED_ORACLE) = {
  module Bee = BeeKemKiOracles(BeeKemProtocolOfPaperInstance(I))
  module Prf = MultiDomainPrfOracle(K, R)
  module Routed = PrfOracleBackedKeySchedule(Prf)
  module Core = AuthoritativeLiveProtocolOracle(Auth, Bee, Routed)
  module Live = AuthoritativePrfBackedLiveOracle(Core, Routed)
  module A = A(Live)

  proc run(
    beekem_bit : bool,
    application_bit : bool
  ) : authoritative_live_application_evidence = {
    var initial_authorization : authorization_state option;
    var initial_authorization_valid : bool;
    var application_challenge_count : int;
    var beekem_safe : bool;
    var authentication_failure : bool;
    var adapter_fault : bool;
    var protocol_failure : bool;
    var adversary_guess : bool;
    var raw_eligible : bool;
    var authenticated_eligible : bool;
    var raw_decision : bool;
    var authenticated_decision : bool;
    var raw_win : bool;
    var authenticated_win : bool;

    initial_authorization <- live_auth_initial_authorization;

    Prf.init(application_bit);
    Bee.initialize(
      authoritative_live_initial_users,
      authoritative_live_initial_group,
      live_auth_retention_kappa,
      authoritative_live_initial_membership,
      beekem_bit
    );
    Routed.init();
    Core.init(
      authoritative_live_initial_registry,
      live_auth_initial_state,
      live_auth_initial_digest
    );

    A.attack();
    adversary_guess <@ A.guess();

    initial_authorization_valid <- initial_authorization <> None;
    application_challenge_count <- challenge_query_count Core.derived_queries;
    beekem_safe <- bee_safe_kappa
      live_auth_retention_kappa
      Bee.Environment.state.`bps_operations
      Bee.Environment.query_log;
    authentication_failure <- Auth.unauthorized_accepted;
    adapter_fault <- Core.runtime_fault;
    protocol_failure <- Bee.Environment.protocol_consistency_failure;
    raw_eligible <- authoritative_live_raw_eligible
      initial_authorization_valid
      application_challenge_count
      beekem_safe
      adapter_fault
      protocol_failure;
    authenticated_eligible <- authoritative_live_authenticated_eligible
      initial_authorization_valid
      application_challenge_count
      beekem_safe
      authentication_failure
      adapter_fault
      protocol_failure;
    raw_decision <- raw_eligible /\ adversary_guess;
    authenticated_decision <- authenticated_eligible /\ adversary_guess;
    raw_win <- raw_decision = application_bit;
    authenticated_win <- authenticated_decision = application_bit;

    return
      {| alae_application_bit = application_bit;
         alae_initial_authorization_valid = initial_authorization_valid;
         alae_application_challenge_count = application_challenge_count;
         alae_beekem_safe = beekem_safe;
         alae_authentication_failure = authentication_failure;
         alae_adapter_fault = adapter_fault;
         alae_protocol_failure = protocol_failure;
         alae_adversary_guess = adversary_guess;
         alae_raw_eligible = raw_eligible;
         alae_authenticated_eligible = authenticated_eligible;
         alae_raw_decision = raw_decision;
         alae_authenticated_decision = authenticated_decision;
         alae_raw_win = raw_win;
         alae_authenticated_win = authenticated_win |};
  }
}.

(* Public authoritative L0 game.  BeeKEM executes its real branch in both
   application worlds; only the application challenge bit changes the live
   KDF response.  The sampled presentation and the fixed-bit projections use
   this same procedure body. *)
module AuthoritativeLiveRealGame(
  A : AUTHORITATIVE_LIVE_KEY_ADVERSARY,
  S : SIGNATURE_SCHEME,
  H : NODE_HASH,
  K : MULTI_DOMAIN_KEY_SCHEDULE,
  R : LIVE_KEY_SAMPLER,
  I : BEEKEM_PAPER_INSTANCE
) = {
  module SO = PG.LoggedSignatureOracle(S)
  module Auth = OriginTrackedCandidateEnvironment(SO, H)
  module E = AuthoritativeLiveApplicationExecution(A, K, R, I, Auth)

  proc main_with_fixed_bit(
    application_bit : bool
  ) : authoritative_live_application_evidence = {
    var evidence : authoritative_live_application_evidence;

    SO.init();
    Auth.init(live_auth_initial_state);
    evidence <@ E.run(true, application_bit);
    return evidence;
  }

  proc main_with_evidence() : authoritative_live_application_evidence = {
    var application_bit : bool;
    var evidence : authoritative_live_application_evidence;

    SO.init();
    Auth.init(live_auth_initial_state);
    application_bit <$ dbool;
    evidence <@ E.run(true, application_bit);
    return evidence;
  }

  proc main() : bool = {
    var evidence : authoritative_live_application_evidence;
    evidence <@ main_with_evidence();
    return evidence.`alae_raw_win;
  }

  proc authenticated_main() : bool = {
    var evidence : authoritative_live_application_evidence;
    evidence <@ main_with_evidence();
    return evidence.`alae_authenticated_win;
  }
}.

(* Deliverable A sees precisely the same sampled-bit authoritative execution.
   The partition game initializes the supplied origin-tracked oracle before
   calling [attack]; this wrapper introduces no authentication premise and does
   not replace the validator. *)
module BAuthoritativeLiveOriginAdversary(
  A : AUTHORITATIVE_LIVE_KEY_ADVERSARY,
  K : MULTI_DOMAIN_KEY_SCHEDULE,
  R : LIVE_KEY_SAMPLER,
  I : BEEKEM_PAPER_INSTANCE
)(Auth : ORIGIN_TRACKED_UNAUTHORIZED_ORACLE) = {
  module E = AuthoritativeLiveApplicationExecution(A, K, R, I, Auth)

  proc attack() : unit = {
    var application_bit : bool;
    var evidence : authoritative_live_application_evidence;

    application_bit <$ dbool;
    evidence <@ E.run(true, application_bit);
  }
}.

section AuthoritativeLiveAuthenticationHop.
  declare module A <: AUTHORITATIVE_LIVE_KEY_ADVERSARY.
  declare module S <: SIGNATURE_SCHEME.
  declare module H <: NODE_HASH.
  declare module K <: MULTI_DOMAIN_KEY_SCHEDULE.
  declare module R <: LIVE_KEY_SAMPLER.
  declare module I <: BEEKEM_PAPER_INSTANCE.

  module L0 = AuthoritativeLiveRealGame(A, S, H, K, R, I).
  module GP = UnauthorizedOriginPartitionGame(
    BAuthoritativeLiveOriginAdversary(A, K, R, I), S, H
  ).
  module EUFOP = PG.MultiUserEUFCMAGame(
    BSignOriginOperationDirect(
      BAuthoritativeLiveOriginAdversary(A, K, R, I), H
    ), S
  ).
  module EUFFACT = PG.MultiUserEUFCMAGame(
    BSignOriginFactWitness(
      BAuthoritativeLiveOriginAdversary(A, K, R, I), H
    ), S
  ).
  module COLL = PG.NodeCollisionGame(
    BHashOrigin(BAuthoritativeLiveOriginAdversary(A, K, R, I), S), H
  ).

  lemma authoritative_live_authentication_failure_exactly_deliverable_a
      &m :
    Pr[
      L0.main_with_evidence() @ &m :
        res.`alae_authentication_failure
    ] =
    Pr[
      GP.main(live_auth_initial_state) @ &m : res.`opr_real
    ].
  proof.
    byequiv
      (_ : ={glob A, glob S, glob H, glob K, glob R, glob I}
           ==>
           res{1}.`alae_authentication_failure = res{2}.`opr_real) => //.
    proc.
    inline *.
    sim.
  qed.

  (* Exact authoritative AuthLoss expansion.  Every nonzero term is one of the
     already-proved Deliverable A primitive games instantiated with the concrete
     canonical live execution above. *)
  lemma authoritative_live_authentication_failure_bound &m :
    Pr[
      L0.main_with_evidence() @ &m :
        res.`alae_authentication_failure
    ] <=
        q_operation_signature_factor *
          Pr[EUFOP.main(live_auth_initial_state) @ &m : res]
      + q_fact_signature_factor *
          Pr[EUFFACT.main(live_auth_initial_state) @ &m : res]
      + Pr[COLL.main(live_auth_initial_state) @ &m : res]
      + encoding_failure_probability.
  proof.
    rewrite authoritative_live_authentication_failure_exactly_deliverable_a.
    exact
      (UnauthorizedOriginFinalBound.adv_unauthorized_origin_bound
         &m live_auth_initial_state).
  qed.
end section AuthoritativeLiveAuthenticationHop.
