require import AllCore List.
require import ProtocolTypes CanonicalEncoding ProtocolPrimitives AuthorizationState.
require import AuthorizationAncestry UnauthorizedSignatureReduction UnauthorizedOriginGame.
require import LiveKeyGame LivePrfTypes LivePrfGame.

import PG.

(* Application key-schedule adapter used by the concrete BPRFLive reduction.
   Live calls reach the primitive challenge oracle; every permitted history
   and constrained-history call is forwarded to the corresponding real-domain
   oracle. *)
module PrfOracleBackedKeySchedule(
  O : MULTI_DOMAIN_PRF_ORACLE
) : MULTI_DOMAIN_KEY_SCHEDULE = {
  proc derive_live(
    secret : beekem_secret,
    label : live_key_label
  ) : live_application_key = {
    var answer : live_application_key;
    answer <@ O.challenge_live(secret, label);
    return answer;
  }

  proc derive_history(
    secret : beekem_secret,
    label : history_key_label
  ) : history_domain_output = {
    var answer : history_domain_output;
    answer <@ O.derive_history(secret, label);
    return answer;
  }

  proc derive_history_capability(
    secret : beekem_secret,
    label : history_key_label,
    cover : segment_cover
  ) : history_capability_output = {
    var answer : history_capability_output;
    answer <@ O.derive_history_capability(secret, label, cover);
    return answer;
  }
}.

(* LiveProtocolCore evaluates both key branches before selecting its application
   bit.  BPRFLive fixes that selector to the real branch, so this deterministic
   value is evaluated but never returned to the application adversary. *)
module PrfReductionUnusedSampler : LIVE_KEY_SAMPLER = {
  proc sample(label : live_key_label) : live_application_key = {
    return LiveApplicationKey 0 label;
  }
}.

(* Concrete application-to-primitive reduction.  [B] is deliberately the
   application BeeKEM runtime seam.  The current admissibility computation is
   provisional and must later be discharged against the authoritative complete
   BeeKEM query log; it is neither supplied by the adversary nor represented by
   a generic Boolean. *)
module BPRFLive(
  A : LIVE_KEY_ADVERSARY,
  S : SIGNATURE_SCHEME,
  H : NODE_HASH,
  B : BEEKEM_LIVE_RUNTIME
)(O : MULTI_DOMAIN_PRF_ORACLE) = {
  module SO = PG.LoggedSignatureOracle(S)
  module Auth = OriginTrackedCandidateEnvironment(SO, H)
  module K = PrfOracleBackedKeySchedule(O)
  module Live = LiveProtocolCore(Auth, B, K, PrfReductionUnusedSampler)
  module A = A(Live)

  proc attack(
    initial_state : protocol_state,
    initial_facts : signed_authorization_fact list,
    retention_kappa : int
  ) : mdprf_adversary_result = {
    var initial_authorization : authorization_state option;
    var initial_digest : authorization_digest;
    var adversary_guess : bool;
    var eligible : bool;

    initial_authorization <-
      live_initial_authorization initial_state initial_facts;
    initial_digest <-
      live_initial_authorization_digest initial_state initial_facts;
    adversary_guess <- false;
    eligible <- false;

    SO.init();
    Auth.init(initial_state);
    Live.init(initial_state, retention_kappa, true, initial_digest);
    A.attack();
    adversary_guess <@ A.guess();

    eligible <-
         initial_authorization <> None
      /\ live_trace_admissible
           retention_kappa Live.relation Live.queries Live.runtime_fault
      /\ ! Auth.unauthorized_accepted;

    return
      {| mpar_eligible = eligible;
         mpar_guess = adversary_guess |};
  }
}.
