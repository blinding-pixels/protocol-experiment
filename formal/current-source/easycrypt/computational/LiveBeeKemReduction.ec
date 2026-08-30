require import AllCore Distr DBool.
require import ProtocolTypes ProtocolPrimitives UnauthorizedSignatureReduction.
require import UnauthorizedOriginGame LiveKeyGame LiveAuthenticationReduction.
require import LiveBeeKemKiInterface LiveBeeKemOracle.

import PG.

(* Concrete L2 reduction adversary.  Its output is the authenticated application
   experiment's success indicator.  In the primitive real-root world this is
   the L1 application experiment; in the random-root world it is the next
   hybrid.  No protocol security conclusion is assumed here. *)
module BBeeLive(
  A : LIVE_KEY_ADVERSARY,
  S : SIGNATURE_SCHEME,
  H : NODE_HASH,
  K : MULTI_DOMAIN_KEY_SCHEDULE,
  R : LIVE_KEY_SAMPLER
)(O : BEEKEM_KI_ORACLE) = {
  module SO = PG.LoggedSignatureOracle(S)
  module Auth = OriginTrackedCandidateEnvironment(SO, H)
  module Live = KiBackedLiveOracle(Auth, O, K, R)
  module A = A(Live)

  proc attack() : bool = {
    var application_bit : bool;
    var adversary_guess : bool;

    SO.init();
    Auth.init(live_auth_initial_state);
    application_bit <$ {0,1};
    Live.init(
      live_auth_initial_state,
      live_auth_retention_kappa,
      application_bit,
      live_auth_initial_digest
    );
    A.attack();
    adversary_guess <@ A.guess();

    return
         live_auth_initial_authorization <> None
      /\ live_trace_admissible
           live_auth_retention_kappa
           Live.D.Base.Core.relation Live.D.queries
           (Live.D.Base.Core.runtime_fault \/ Live.D.Base.runtime_fault)
      /\ ! Auth.unauthorized_accepted
      /\ adversary_guess = application_bit;
  }
}.
