require import AllCore List FSet Distr.
require import ProtocolTypes CanonicalEncoding ProtocolPrimitives AuthorizationState.
require import AuthorizationAncestry UnauthorizedSignatureReduction UnauthorizedOriginGame.
require import LiveKeyGame LivePrfTypes LivePrfGame LivePrfApplicationReduction.

import PG.

(* Direct authenticated application fixed-bit projection.  This is the same
   application execution used by L0/L1, with the Deliverable A unauthorized
   event excluded in the challenger-computed eligibility gate.  It exposes the
   one-event used by the fixed-bit PRF distance without introducing a second
   safety predicate. *)
module AuthenticatedApplicationBit(
  A : LIVE_KEY_ADVERSARY,
  S : SIGNATURE_SCHEME,
  H : NODE_HASH,
  B : BEEKEM_LIVE_RUNTIME,
  K : MULTI_DOMAIN_KEY_SCHEDULE,
  R : LIVE_KEY_SAMPLER
) = {
  module SO = PG.LoggedSignatureOracle(S)
  module Auth = OriginTrackedCandidateEnvironment(SO, H)
  module O = LiveProtocolCore(Auth, B, K, R)
  module A = A(O)

  proc main(
    initial_state : protocol_state,
    initial_facts : signed_authorization_fact list,
    retention_kappa : int,
    challenge_bit : bool
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
    O.init(initial_state, retention_kappa, challenge_bit, initial_digest);
    A.attack();
    adversary_guess <@ A.guess();

    eligible <-
         initial_authorization <> None
      /\ live_trace_admissible
           retention_kappa O.relation O.queries O.runtime_fault
      /\ ! Auth.unauthorized_accepted;

    return
      {| mpar_eligible = eligible;
         mpar_guess = adversary_guess |};
  }
}.

section ApplicationPrfExactHop.
  declare module A <: LIVE_KEY_ADVERSARY.
  declare module S <: SIGNATURE_SCHEME.
  declare module H <: NODE_HASH.
  declare module B <: BEEKEM_LIVE_RUNTIME.
  declare module K <: MULTI_DOMAIN_KEY_SCHEDULE.
  declare module R <: LIVE_KEY_SAMPLER.

  module Direct = AuthenticatedApplicationBit(A, S, H, B, K, R).
  module Prf = MultiDomainPrfGame(BPRFLive(A, S, H, B), K, R).

  (* The PRF reduction preserves the exact application execution.  Ordinary
     live reveals call the real-only primitive procedure; only the application
     challenge is switched by the primitive bit.  Authentication state,
     provisional admissibility state, adversary guess, and K/R call order are
     therefore identical. *)
  lemma application_fixed_bit_one_event_exactly_prf
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
             challenge_bit, glob A, glob S, glob H, glob B, glob K, glob R}
           ==>
           (res{1}.`mpar_eligible /\ res{1}.`mpar_guess) =
           (res{2}.`mpge_eligible /\ res{2}.`mpge_guess)) => //.
    proc.
    inline *.
    sim.
  qed.

  lemma application_fixed_bit_advantage_exactly_prf
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
      (application_fixed_bit_one_event_exactly_prf
         &m initial_state initial_facts retention_kappa true)
      (application_fixed_bit_one_event_exactly_prf
         &m initial_state initial_facts retention_kappa false).
    by done.
  qed.
end section ApplicationPrfExactHop.
