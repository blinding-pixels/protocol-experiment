require import AllCore List.
require import ProtocolTypes CanonicalEncoding ProtocolPrimitives.
require import LiveKeyGame LivePrfTypes LivePrfGame.
require import LivePrfApplicationReduction.

(* Bit-free ideal oracle.  Live challenges are sampled once from the ideal
   live-key sampler.  History and constrained-history queries remain on the
   real multi-domain schedule, and every query retains the same typed log shape
   used by the primitive game.  No hidden bit is stored or consulted here. *)
module MultiDomainPrfIdealOracle(
  K : MULTI_DOMAIN_KEY_SCHEDULE,
  R : LIVE_KEY_SAMPLER
) = {
  var queries : mdprf_query list

  proc init() : unit = {
    queries <- [];
  }

  proc challenge_live(
    secret : beekem_secret,
    label : live_key_label
  ) : live_application_key = {
    var answer : live_application_key;

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

(* Fixed-bit projection of the ideal oracle.  The marker is retained only so
   this procedure has the same two experiments needed by the fixed-bit
   advantage definition; it is intentionally not passed to the oracle or the
   adversary. *)
module MultiDomainPrfIdealProjection(
  A : MULTI_DOMAIN_PRF_ADVERSARY,
  K : MULTI_DOMAIN_KEY_SCHEDULE,
  R : LIVE_KEY_SAMPLER
) = {
  module O = MultiDomainPrfIdealOracle(K, R)
  module A = A(O)

  proc main(
    initial_state : protocol_state,
    initial_facts : signed_authorization_fact list,
    retention_kappa : int,
    challenge_bit : bool
  ) : mdprf_adversary_result = {
    var result : mdprf_adversary_result;

    O.init();
    result <@ A.attack(initial_state, initial_facts, retention_kappa);
    return result;
  }
}.

section MultiDomainPrfIdealIndependence.
  declare module A <: MULTI_DOMAIN_PRF_ADVERSARY.
  declare module K <: MULTI_DOMAIN_KEY_SCHEDULE.
  declare module R <: LIVE_KEY_SAMPLER.

  module G = MultiDomainPrfIdealProjection(A, K, R).

  lemma ideal_fixed_bit_one_event_equal
      &m
      (initial_state : protocol_state)
      (initial_facts : signed_authorization_fact list)
      (retention_kappa : int) :
    Pr[
      G.main(initial_state, initial_facts, retention_kappa, true) @ &m :
      res.`mpar_eligible /\ res.`mpar_guess
    ] =
    Pr[
      G.main(initial_state, initial_facts, retention_kappa, false) @ &m :
      res.`mpar_eligible /\ res.`mpar_guess
    ].
  proof.
    byequiv
      (_ : ={initial_state, initial_facts, retention_kappa,
             glob A, glob K, glob R} ==> res{1} = res{2}) => //.
    proc.
    inline *.
    sim.
  qed.

  lemma ideal_fixed_bit_advantage_zero
      &m
      (initial_state : protocol_state)
      (initial_facts : signed_authorization_fact list)
      (retention_kappa : int) :
    mdprf_fixed_bit_advantage
      (Pr[
         G.main(initial_state, initial_facts, retention_kappa, true) @ &m :
         res.`mpar_eligible /\ res.`mpar_guess
       ])
      (Pr[
         G.main(initial_state, initial_facts, retention_kappa, false) @ &m :
         res.`mpar_eligible /\ res.`mpar_guess
       ]) = 0%r.
  proof.
    rewrite /mdprf_fixed_bit_advantage
      (ideal_fixed_bit_one_event_equal
         &m initial_state initial_facts retention_kappa).
    by smt().
  qed.
end section MultiDomainPrfIdealIndependence.

section ApplicationIdealIndependence.
  declare module A <: LIVE_KEY_ADVERSARY.
  declare module S <: SIGNATURE_SCHEME.
  declare module H <: NODE_HASH.
  declare module B <: BEEKEM_LIVE_RUNTIME.
  declare module K <: MULTI_DOMAIN_KEY_SCHEDULE.
  declare module R <: LIVE_KEY_SAMPLER.

  module AppIdeal = MultiDomainPrfIdealProjection(
    BPRFLive(A, S, H, B), K, R
  ).

  (* This is the application ideal-zero boundary.  It executes the exact
     application reduction, including Deliverable A authentication state,
     provisional BeeKEM runtime seam, history-query simulation, and the
     challenger-computed eligibility gate.  The two fixed-bit experiments are
     equal because the ideal live-key oracle has no bit-dependent state or
     response. *)
  lemma application_ideal_fixed_bit_one_event_equal
      &m
      (initial_state : protocol_state)
      (initial_facts : signed_authorization_fact list)
      (retention_kappa : int) :
    Pr[
      AppIdeal.main(
        initial_state, initial_facts, retention_kappa, true
      ) @ &m : res.`mpar_eligible /\ res.`mpar_guess
    ] =
    Pr[
      AppIdeal.main(
        initial_state, initial_facts, retention_kappa, false
      ) @ &m : res.`mpar_eligible /\ res.`mpar_guess
    ].
  proof.
    byequiv
      (_ : ={initial_state, initial_facts, retention_kappa,
             glob A, glob S, glob H, glob B, glob K, glob R} ==>
           res{1} = res{2}) => //.
    proc.
    inline *.
    sim.
  qed.

  lemma application_ideal_live_key_advantage_zero
      &m
      (initial_state : protocol_state)
      (initial_facts : signed_authorization_fact list)
      (retention_kappa : int) :
    mdprf_fixed_bit_advantage
      (Pr[
         AppIdeal.main(
           initial_state, initial_facts, retention_kappa, true
         ) @ &m : res.`mpar_eligible /\ res.`mpar_guess
       ])
      (Pr[
         AppIdeal.main(
           initial_state, initial_facts, retention_kappa, false
         ) @ &m : res.`mpar_eligible /\ res.`mpar_guess
       ]) = 0%r.
  proof.
    rewrite /mdprf_fixed_bit_advantage
      (application_ideal_fixed_bit_one_event_equal
         &m initial_state initial_facts retention_kappa).
    by smt().
  qed.
end section ApplicationIdealIndependence.
