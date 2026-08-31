require import AllCore List FSet.
require import ProtocolTypes ProtocolPrimitives.
require import LivePrfGame LivePrfAuthoritativeReduction.

section AuthoritativeApplicationPrfExactHop.
  declare module A <: AUTHORITATIVE_LIVE_KEY_ADVERSARY.
  declare module S <: SIGNATURE_SCHEME.
  declare module H <: NODE_HASH.
  declare module K <: MULTI_DOMAIN_KEY_SCHEDULE.
  declare module R <: LIVE_KEY_SAMPLER.
  declare module I <: BEEKEM_PAPER_INSTANCE.

  module Direct = AuthoritativePrfApplicationBit(A, S, H, K, R, I).
  module Prf = MultiDomainPrfGame(
    BPRFLiveAuthoritative(A, S, H, I), K, R
  ).

  (* The direct H1/H2 endpoint and the concrete primitive game run the same
     production authorization oracle, canonical BeeKEM graph and query log,
     full-state compromise interface, adversary, KDF, sampler, and call order.
     Only the primitive game packages the result into evidence. *)
  lemma authoritative_application_fixed_bit_one_event_exactly_prf
      &m
      (initial_state : protocol_state)
      (initial_facts : signed_authorization_fact list)
      (retention_kappa : int)
      (challenge_bit : bool) :
    Pr[
      Direct.main(
        initial_state, initial_facts, retention_kappa, challenge_bit
      ) @ &m : res.`mpar_eligible /\ res.`mpar_guess
    ] =
    Pr[
      Prf.main_with_fixed_bit(
        initial_state, initial_facts, retention_kappa, challenge_bit
      ) @ &m : res.`mpge_eligible /\ res.`mpge_guess
    ].
  proof.
    byequiv
      (_ : ={initial_state, initial_facts, retention_kappa,
             challenge_bit, glob A, glob S, glob H, glob K, glob R, glob I}
           ==>
           (res{1}.`mpar_eligible /\ res{1}.`mpar_guess) =
           (res{2}.`mpge_eligible /\ res{2}.`mpge_guess)) => //.
    proc.
    inline *.
    sim.
  qed.

  lemma authoritative_application_fixed_bit_advantage_exactly_prf
      &m
      (initial_state : protocol_state)
      (initial_facts : signed_authorization_fact list)
      (retention_kappa : int) :
    mdprf_fixed_bit_advantage
      (Pr[
         Direct.main(
           initial_state, initial_facts, retention_kappa, true
         ) @ &m : res.`mpar_eligible /\ res.`mpar_guess
       ])
      (Pr[
         Direct.main(
           initial_state, initial_facts, retention_kappa, false
         ) @ &m : res.`mpar_eligible /\ res.`mpar_guess
       ]) =
    mdprf_fixed_bit_advantage
      (Pr[
         Prf.main_with_fixed_bit(
           initial_state, initial_facts, retention_kappa, true
         ) @ &m : res.`mpge_eligible /\ res.`mpge_guess
       ])
      (Pr[
         Prf.main_with_fixed_bit(
           initial_state, initial_facts, retention_kappa, false
         ) @ &m : res.`mpge_eligible /\ res.`mpge_guess
       ]).
  proof.
    rewrite
      (authoritative_application_fixed_bit_one_event_exactly_prf
         &m initial_state initial_facts retention_kappa true)
      (authoritative_application_fixed_bit_one_event_exactly_prf
         &m initial_state initial_facts retention_kappa false).
    by done.
  qed.
end section AuthoritativeApplicationPrfExactHop.
