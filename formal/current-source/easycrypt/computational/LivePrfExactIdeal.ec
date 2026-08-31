require import AllCore List.
require import ProtocolTypes CanonicalEncoding ProtocolPrimitives.
require import LiveKeyGame BeeKemConstruction.
require import LivePrfTypes LivePrfGame.
require import LiveBeeKemAuthoritativeLiveTypes.
require import LivePrfAuthoritativeReduction.

(* Exact bit-free ideal for the multi-domain PRF game.  The distinguished live
   challenge executes the same KDF call and sampler call, in the same order, as
   the random fixed-bit world, but discards the real KDF result and returns only
   the independent sample.  Preserving the discarded call is load-bearing when
   the supplied key-schedule module carries state. *)
module MultiDomainPrfExactIdealOracle(
  K : MULTI_DOMAIN_KEY_SCHEDULE,
  R : LIVE_KEY_SAMPLER
) = {
  var queries : mdprf_query list

  proc init() : unit = {
    queries <- [];
  }

  proc derive_live(
    secret : beekem_secret,
    label : live_key_label
  ) : live_application_key = {
    var answer : live_application_key;

    answer <@ K.derive_live(secret, label);
    queries <- rcons queries
      {| mpq_kind = MdPrfLiveQuery
           {| mpli_secret = secret; mpli_label = label |} |};
    return answer;
  }

  proc challenge_live(
    secret : beekem_secret,
    label : live_key_label
  ) : live_application_key = {
    var discarded_real : live_application_key;
    var answer : live_application_key;

    discarded_real <@ K.derive_live(secret, label);
    answer <@ R.sample(label);
    queries <- rcons queries
      {| mpq_kind = MdPrfLiveChallenge
           {| mpli_secret = secret; mpli_label = label |} |};
    return answer;
  }

  proc derive_history(
    secret : beekem_secret,
    label : history_key_label
  ) : history_domain_output = {
    var answer : history_domain_output;

    answer <@ K.derive_history(secret, label);
    queries <- rcons queries
      {| mpq_kind = MdPrfHistoryQuery
           {| mphi_secret = secret; mphi_label = label |} |};
    return answer;
  }

  proc derive_history_capability(
    secret : beekem_secret,
    label : history_key_label,
    cover : segment_cover
  ) : history_capability_output = {
    var answer : history_capability_output;

    answer <@ K.derive_history_capability(secret, label, cover);
    queries <- rcons queries
      {| mpq_kind = MdPrfHistoryCapabilityQuery
           {| mphci_secret = secret;
              mphci_label = label;
              mphci_cover = cover |} |};
    return answer;
  }
}.

module MultiDomainPrfExactIdealProjection(
  A : MULTI_DOMAIN_PRF_ADVERSARY,
  K : MULTI_DOMAIN_KEY_SCHEDULE,
  R : LIVE_KEY_SAMPLER
) = {
  module O = MultiDomainPrfExactIdealOracle(K, R)
  module A = A(O)

  proc main(
    initial_state : protocol_state,
    initial_facts : signed_authorization_fact list,
    retention_kappa : int,
    challenge_marker : bool
  ) : mdprf_adversary_result = {
    var result : mdprf_adversary_result;

    O.init();
    result <@ A.attack(initial_state, initial_facts, retention_kappa);
    return result;
  }
}.

section MultiDomainPrfExactIdealHop.
  declare module A <: MULTI_DOMAIN_PRF_ADVERSARY.
  declare module K <: MULTI_DOMAIN_KEY_SCHEDULE.
  declare module R <: LIVE_KEY_SAMPLER.

  module Prf = MultiDomainPrfGame(A, K, R).
  module Ideal = MultiDomainPrfExactIdealProjection(A, K, R).

  lemma mdprf_random_fixed_bit_one_event_exactly_ideal
      &m
      (initial_state : protocol_state)
      (initial_facts : signed_authorization_fact list)
      (retention_kappa : int)
      (challenge_marker : bool) :
    Pr[
      Prf.main_with_fixed_bit(
        initial_state, initial_facts, retention_kappa, false
      ) @ &m : res.`mpge_eligible /\ res.`mpge_guess
    ] =
    Pr[
      Ideal.main(
        initial_state, initial_facts, retention_kappa, challenge_marker
      ) @ &m : res.`mpar_eligible /\ res.`mpar_guess
    ].
  proof.
    byequiv
      (_ : ={initial_state, initial_facts, retention_kappa,
             glob A, glob K, glob R}
           ==>
           (res{1}.`mpge_eligible /\ res{1}.`mpge_guess) =
           (res{2}.`mpar_eligible /\ res{2}.`mpar_guess)) => //.
    proc.
    inline *.
    sim.
  qed.

  lemma mdprf_exact_ideal_fixed_bit_one_event_equal
      &m
      (initial_state : protocol_state)
      (initial_facts : signed_authorization_fact list)
      (retention_kappa : int) :
    Pr[
      Ideal.main(
        initial_state, initial_facts, retention_kappa, true
      ) @ &m : res.`mpar_eligible /\ res.`mpar_guess
    ] =
    Pr[
      Ideal.main(
        initial_state, initial_facts, retention_kappa, false
      ) @ &m : res.`mpar_eligible /\ res.`mpar_guess
    ].
  proof.
    byequiv
      (_ : ={initial_state, initial_facts, retention_kappa,
             glob A, glob K, glob R} ==> res{1} = res{2}) => //.
    proc.
    inline *.
    sim.
  qed.

  lemma mdprf_exact_ideal_fixed_bit_advantage_zero
      &m
      (initial_state : protocol_state)
      (initial_facts : signed_authorization_fact list)
      (retention_kappa : int) :
    mdprf_fixed_bit_advantage
      (Pr[
         Ideal.main(
           initial_state, initial_facts, retention_kappa, true
         ) @ &m : res.`mpar_eligible /\ res.`mpar_guess
       ])
      (Pr[
         Ideal.main(
           initial_state, initial_facts, retention_kappa, false
         ) @ &m : res.`mpar_eligible /\ res.`mpar_guess
       ]) = 0%r.
  proof.
    rewrite /mdprf_fixed_bit_advantage
      (mdprf_exact_ideal_fixed_bit_one_event_equal
         &m initial_state initial_facts retention_kappa).
    by smt().
  qed.
end section MultiDomainPrfExactIdealHop.

section AuthoritativeApplicationExactIdealHop.
  declare module A <: AUTHORITATIVE_LIVE_KEY_ADVERSARY.
  declare module S <: SIGNATURE_SCHEME.
  declare module H <: NODE_HASH.
  declare module K <: MULTI_DOMAIN_KEY_SCHEDULE.
  declare module R <: LIVE_KEY_SAMPLER.
  declare module I <: BEEKEM_PAPER_INSTANCE.

  module AuthoritativePrf = MultiDomainPrfGame(
    BPRFLiveAuthoritative(A, S, H, I), K, R
  ).
  module AuthoritativeIdeal = MultiDomainPrfExactIdealProjection(
    BPRFLiveAuthoritative(A, S, H, I), K, R
  ).

  lemma authoritative_prf_random_fixed_bit_exactly_ideal
      &m :
    Pr[
      AuthoritativePrf.main_with_fixed_bit(
        live_auth_initial_state,
        live_auth_initial_facts,
        live_auth_retention_kappa,
        false
      ) @ &m : res.`mpge_eligible /\ res.`mpge_guess
    ] =
    Pr[
      AuthoritativeIdeal.main(
        live_auth_initial_state,
        live_auth_initial_facts,
        live_auth_retention_kappa,
        false
      ) @ &m : res.`mpar_eligible /\ res.`mpar_guess
    ].
  proof.
    exact
      (mdprf_random_fixed_bit_one_event_exactly_ideal
         (BPRFLiveAuthoritative(A, S, H, I)) K R &m
         live_auth_initial_state
         live_auth_initial_facts
         live_auth_retention_kappa
         false).
  qed.

  lemma authoritative_exact_ideal_live_key_advantage_zero
      &m :
    mdprf_fixed_bit_advantage
      (Pr[
         AuthoritativeIdeal.main(
           live_auth_initial_state,
           live_auth_initial_facts,
           live_auth_retention_kappa,
           true
         ) @ &m : res.`mpar_eligible /\ res.`mpar_guess
       ])
      (Pr[
         AuthoritativeIdeal.main(
           live_auth_initial_state,
           live_auth_initial_facts,
           live_auth_retention_kappa,
           false
         ) @ &m : res.`mpar_eligible /\ res.`mpar_guess
       ]) = 0%r.
  proof.
    exact
      (mdprf_exact_ideal_fixed_bit_advantage_zero
         (BPRFLiveAuthoritative(A, S, H, I)) K R &m
         live_auth_initial_state
         live_auth_initial_facts
         live_auth_retention_kappa).
  qed.
end section AuthoritativeApplicationExactIdealHop.
