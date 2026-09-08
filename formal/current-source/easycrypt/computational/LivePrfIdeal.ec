require import AllCore List.
require import ProtocolTypes CanonicalEncoding ProtocolPrimitives.
require import LiveKeyGame LivePrfTypes LivePrfGame.
require import LivePrfApplicationReduction.

(* Bit-free ideal oracle.  Permitted live reveals remain on the real key
   schedule.  Only the distinguished live challenge is sampled from the ideal
   live-key sampler.  History and constrained-history queries remain real, and
   every call retains the same typed log shape used by the primitive game.
   No hidden bit is stored or consulted here. *)
module MultiDomainPrfIdealOracle(
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

(* The closed session contains the exact initialization and attack procedures.
   There are no module-state exclusions on this interface.  Treating all of its
   state together permits self-composition even when the constituent modules
   share state. *)
module type IDEAL_PRF_SESSION = {
  proc init() : unit
  proc attack(initial_state : protocol_state,
              initial_facts : signed_authorization_fact list,
              retention_kappa : int) : mdprf_adversary_result
}.

module IdealPrfBitMarker(D : IDEAL_PRF_SESSION) = {
  proc main(initial_state : protocol_state,
            initial_facts : signed_authorization_fact list,
            retention_kappa : int,
            challenge_bit : bool) : mdprf_adversary_result = {
    var result : mdprf_adversary_result;
    D.init();
    result <@ D.attack(initial_state, initial_facts, retention_kappa);
    return result;
  }
}.

section IdealPrfBitMarkerIndependence.
  declare module D <: IDEAL_PRF_SESSION.
  lemma ideal_prf_marker_unused &m
      (state : protocol_state) (facts : signed_authorization_fact list)
      (kappa : int) :
    Pr[IdealPrfBitMarker(D).main(state, facts, kappa, true) @ &m :
      res.`mpar_eligible /\ res.`mpar_guess] =
    Pr[IdealPrfBitMarker(D).main(state, facts, kappa, false) @ &m :
      res.`mpar_eligible /\ res.`mpar_guess].
  proof.
    byequiv (_ : ={initial_state, initial_facts, retention_kappa, glob D}
                   ==> ={res}) => //.
    proc.
    call (_ : true).
    call (_ : true).
    by auto.
  qed.
end section IdealPrfBitMarkerIndependence.

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

  module Session = {
    proc init = O.init
    proc attack = A.attack
  }
  proc main = IdealPrfBitMarker(Session).main
}.

section MultiDomainPrfIdealIndependence.
  declare module A <: MULTI_DOMAIN_PRF_ADVERSARY.
  declare module K <: MULTI_DOMAIN_KEY_SCHEDULE.
  declare module R <: LIVE_KEY_SAMPLER.

  module G = MultiDomainPrfIdealProjection(A, K, R).

  (* Checked definitional bridge: all observations of the public endpoint use
     the session whose two procedures alias the original oracle and adversary. *)
  lemma ideal_public_projection_exactly_session
      &m (state : protocol_state) (facts : signed_authorization_fact list)
      (kappa : int) (bit : bool) (event : mdprf_adversary_result -> bool) :
    Pr[G.main(state, facts, kappa, bit) @ &m : event res] =
    Pr[IdealPrfBitMarker(G.Session).main(state, facts, kappa, bit) @ &m :
      event res].
  proof. by done. qed.

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
    exact (ideal_prf_marker_unused G.Session
      &m initial_state initial_facts retention_kappa).
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
    exact (ideal_fixed_bit_one_event_equal (BPRFLive(A, S, H, B)) K R
      &m initial_state initial_facts retention_kappa).
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
