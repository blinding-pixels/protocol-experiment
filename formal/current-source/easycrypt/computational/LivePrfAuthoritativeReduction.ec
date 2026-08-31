require import AllCore List FSet.
require import ProtocolTypes CanonicalEncoding ProtocolPrimitives AuthorizationState.
require import AuthorizationAncestry UnauthorizedSignatureReduction UnauthorizedOriginGame.
require import LiveKeyGame LiveAuthenticationReduction.
require import BeeKemTypes BeeKemProtocol BeeKemQueryLog BeeKemSafety BeeKemKiGame.
require import BeeKemConstruction.
require import LivePrfTypes LivePrfGame LivePrfApplicationReduction.
require import LivePrfAuthoritativeAdapter.
require import LiveBeeKemAuthoritativeTypes.
require import LiveBeeKemAuthoritativeLiveTypes.
require import LiveBeeKemAuthoritativeLiveOracle.

import PG.

(* Shared concrete application-to-BeeKEM configuration.  The registry, user
   universe, and initial dynamic-group-membership function are ordinary game
   parameters.  They are reused definitionally by the BeeKEM and PRF reductions
   so the two hybrid hops cannot silently initialize different executions. *)
op authoritative_live_initial_registry : application_user_registry.
op authoritative_live_initial_users : beekem_user list.
op authoritative_live_initial_membership : beekem_dgm.

op authoritative_live_group_of_state
    (initial_state : protocol_state) : beekem_group =
  application_group_of_document initial_state.`ps_document_id.

op authoritative_live_initial_group : beekem_group =
  authoritative_live_group_of_state live_auth_initial_state.

(* Challenger-computed eligibility for the authenticated application hybrids.
   A distinguished application live challenge must actually occur.  BeeKEM
   safety is evaluated from the complete canonical operation graph and query
   log.  Authentication and adapter faults are read from the shared executable
   environments rather than supplied by the adversary. *)
op authoritative_live_eligible
    (initial_authorization_valid : bool)
    (application_challenge_count : int)
    (beekem_safe : bool)
    (authentication_failure : bool)
    (adapter_fault : bool) : bool =
     initial_authorization_valid
  /\ 0 < application_challenge_count
  /\ beekem_safe
  /\ ! authentication_failure
  /\ ! adapter_fault.

(* Direct H1/H2 endpoint.  BeeKEM is fixed to its random-root branch and the
   PRF bit alone selects real KDF output or an independent ideal live key.  All
   permitted live reveals, history disclosures, capability disclosures, and
   full-state compromises traverse the same authoritative application oracle. *)
module AuthoritativePrfApplicationBit(
  A : AUTHORITATIVE_LIVE_KEY_ADVERSARY,
  S : SIGNATURE_SCHEME,
  H : NODE_HASH,
  K : MULTI_DOMAIN_KEY_SCHEDULE,
  R : LIVE_KEY_SAMPLER,
  I : BEEKEM_PAPER_INSTANCE
) = {
  module Bee = BeeKemKiOracles(BeeKemProtocolOfPaperInstance(I))
  module O = MultiDomainPrfOracle(K, R)
  module SO = PG.LoggedSignatureOracle(S)
  module Auth = OriginTrackedCandidateEnvironment(SO, H)
  module Routed = PrfOracleBackedKeySchedule(O)
  module Core = AuthoritativeLiveProtocolOracle(Auth, Bee, Routed)
  module Live = AuthoritativePrfBackedLiveOracle(Core, Routed)
  module A = A(Live)

  var initial_authorization_valid : bool
  var application_challenge_count : int
  var beekem_safe : bool
  var authentication_failure : bool
  var adapter_fault : bool
  var protocol_failure : bool
  var adversary_guess : bool
  var endpoint_guess : bool
  var eligible : bool

  proc main(
    initial_state : protocol_state,
    initial_facts : signed_authorization_fact list,
    retention_kappa : int,
    challenge_bit : bool
  ) : mdprf_adversary_result = {
    var initial_authorization : authorization_state option;
    var initial_digest : authorization_digest;

    initial_authorization <-
      live_initial_authorization initial_state initial_facts;
    initial_digest <-
      live_initial_authorization_digest initial_state initial_facts;

    O.init(challenge_bit);
    SO.init();
    Auth.init(initial_state);
    Bee.initialize(
      authoritative_live_initial_users,
      authoritative_live_group_of_state initial_state,
      retention_kappa,
      authoritative_live_initial_membership,
      false
    );
    Routed.init();
    Core.init(
      authoritative_live_initial_registry,
      initial_state,
      initial_digest
    );

    A.attack();
    adversary_guess <@ A.guess();

    initial_authorization_valid <- initial_authorization <> None;
    application_challenge_count <- challenge_query_count Core.derived_queries;
    beekem_safe <- bee_safe_kappa
      retention_kappa
      Bee.Environment.state.`bps_operations
      Bee.Environment.query_log;
    authentication_failure <- Auth.unauthorized_accepted;
    adapter_fault <- Core.runtime_fault;
    protocol_failure <- Bee.Environment.protocol_consistency_failure;
    endpoint_guess <- protocol_failure \/ adversary_guess;
    eligible <- authoritative_live_eligible
      initial_authorization_valid
      application_challenge_count
      beekem_safe
      authentication_failure
      adapter_fault;

    return
      {| mpar_eligible = eligible;
         mpar_guess = endpoint_guess |};
  }
}.

(* Concrete multi-domain PRF adversary.  Its BeeKEM root branch is fixed to the
   same H1 random-root execution as [AuthoritativePrfApplicationBit].  Only an
   accepted application live challenge invokes [O.challenge_live]; every other
   derivation is routed to its real primitive domain. *)
module BPRFLiveAuthoritative(
  A : AUTHORITATIVE_LIVE_KEY_ADVERSARY,
  S : SIGNATURE_SCHEME,
  H : NODE_HASH,
  I : BEEKEM_PAPER_INSTANCE
)(O : MULTI_DOMAIN_PRF_ORACLE) = {
  module Bee = BeeKemKiOracles(BeeKemProtocolOfPaperInstance(I))
  module SO = PG.LoggedSignatureOracle(S)
  module Auth = OriginTrackedCandidateEnvironment(SO, H)
  module Routed = PrfOracleBackedKeySchedule(O)
  module Core = AuthoritativeLiveProtocolOracle(Auth, Bee, Routed)
  module Live = AuthoritativePrfBackedLiveOracle(Core, Routed)
  module A = A(Live)

  proc attack(
    initial_state : protocol_state,
    initial_facts : signed_authorization_fact list,
    retention_kappa : int
  ) : mdprf_adversary_result = {
    var initial_authorization : authorization_state option;
    var initial_digest : authorization_digest;
    var initial_authorization_valid : bool;
    var application_challenge_count : int;
    var beekem_safe : bool;
    var authentication_failure : bool;
    var adapter_fault : bool;
    var protocol_failure : bool;
    var adversary_guess : bool;
    var endpoint_guess : bool;
    var eligible : bool;

    initial_authorization <-
      live_initial_authorization initial_state initial_facts;
    initial_digest <-
      live_initial_authorization_digest initial_state initial_facts;

    SO.init();
    Auth.init(initial_state);
    Bee.initialize(
      authoritative_live_initial_users,
      authoritative_live_group_of_state initial_state,
      retention_kappa,
      authoritative_live_initial_membership,
      false
    );
    Routed.init();
    Core.init(
      authoritative_live_initial_registry,
      initial_state,
      initial_digest
    );

    A.attack();
    adversary_guess <@ A.guess();

    initial_authorization_valid <- initial_authorization <> None;
    application_challenge_count <- challenge_query_count Core.derived_queries;
    beekem_safe <- bee_safe_kappa
      retention_kappa
      Bee.Environment.state.`bps_operations
      Bee.Environment.query_log;
    authentication_failure <- Auth.unauthorized_accepted;
    adapter_fault <- Core.runtime_fault;
    protocol_failure <- Bee.Environment.protocol_consistency_failure;
    endpoint_guess <- protocol_failure \/ adversary_guess;
    eligible <- authoritative_live_eligible
      initial_authorization_valid
      application_challenge_count
      beekem_safe
      authentication_failure
      adapter_fault;

    return
      {| mpar_eligible = eligible;
         mpar_guess = endpoint_guess |};
  }
}.
