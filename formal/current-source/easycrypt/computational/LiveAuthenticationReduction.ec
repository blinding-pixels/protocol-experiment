require import AllCore List FSet.
require import ProtocolTypes CanonicalEncoding ProtocolPrimitives AuthorizationState.
require import AuthorizationAncestry UnauthorizedOriginGame.
require PrimitiveGames.
clone import PrimitiveGames as PG.
require import UnauthorizedOriginPartition UnauthorizedOriginFinalBound.
require import OriginOperationDirectInvariant OriginFactReductionWitness.
require import UnauthorizedOriginHashReduction LiveKeyGame.

import PG.

(* Deliverable A is a suffix theorem over an already materialized public
   protocol state.  These abstract values are ordinary universally quantified
   game parameters, not cryptographic assumptions: no property of them is
   postulated.  In particular, malformed initial authorization data simply
   makes the live experiment ineligible below. *)
op live_auth_initial_state : protocol_state.
op live_auth_initial_facts : signed_authorization_fact list.
op live_auth_retention_kappa : int.

op live_auth_initial_authorization : authorization_state option =
  authorization_policy_replay
    live_auth_initial_state.`ps_creator
    live_auth_initial_facts.

op live_auth_initial_digest : authorization_digest =
  if live_auth_initial_authorization = None
  then InvalidAuthorizationDigest 0
  else authorization_digest_of (oget live_auth_initial_authorization).

(* This is the concrete live adversary installed inside Deliverable A's exact
   origin-tracked oracle.  Every application signing or submission call is
   forwarded by [LiveProtocolCore] to [Auth]; the production validator and its
   A0--A5 origin partition therefore observe the same adaptive live execution.
   The adversary's final guess is consumed, and the hidden bit is sampled here
   rather than supplied by the protocol adversary. *)
module BLiveAuthentication(
  A : LIVE_KEY_ADVERSARY,
  B : BEEKEM_LIVE_RUNTIME,
  K : MULTI_DOMAIN_KEY_SCHEDULE,
  R : LIVE_KEY_SAMPLER
)(Auth : ORIGIN_TRACKED_UNAUTHORIZED_ORACLE) = {
  module O = LiveProtocolCore(Auth, B, K, R)
  module A = A(O)

  var challenge_bit : bool
  var adversary_guess : bool
  var live_success : bool

  proc attack() : unit = {
    challenge_bit <$ {0,1};
    adversary_guess <- false;
    live_success <- false;

    O.init(
      live_auth_initial_state,
      live_auth_retention_kappa,
      challenge_bit,
      live_auth_initial_digest
    );
    A.attack();
    adversary_guess <@ A.guess();

    live_success <-
         live_auth_initial_authorization <> None
      /\ live_trace_admissible
           live_auth_retention_kappa
           O.relation O.queries O.runtime_fault
      /\ adversary_guess = challenge_bit;
  }
}.

type live_authentication_result = {
  lar_live_success : bool;
  lar_authentication_failure : bool;
  lar_bad_operation : bool;
  lar_bad_fact : bool;
  lar_ideal : bool
}.

module LiveAuthenticationGame(
  A : LIVE_KEY_ADVERSARY,
  S : SIGNATURE_SCHEME,
  H : NODE_HASH,
  B : BEEKEM_LIVE_RUNTIME,
  K : MULTI_DOMAIN_KEY_SCHEDULE,
  R : LIVE_KEY_SAMPLER
) = {
  module GP = UnauthorizedOriginPartitionGame(
    BLiveAuthentication(A, B, K, R), S, H
  )

  proc main() : live_authentication_result = {
    var partition : origin_partition_result;

    partition <@ GP.main(live_auth_initial_state);
    return
      {| lar_live_success = GP.A.live_success;
         lar_authentication_failure = partition.`opr_real;
         lar_bad_operation = partition.`opr_bad_operation;
         lar_bad_fact = partition.`opr_bad_fact;
         lar_ideal = partition.`opr_ideal |};
  }
}.

section LiveAuthenticationHop.
  declare module A <: LIVE_KEY_ADVERSARY.
  declare module S <: SIGNATURE_SCHEME.
  declare module H <: NODE_HASH.
  declare module B <: BEEKEM_LIVE_RUNTIME.
  declare module K <: MULTI_DOMAIN_KEY_SCHEDULE.
  declare module R <: LIVE_KEY_SAMPLER.

  module LAG = LiveAuthenticationGame(A, S, H, B, K, R).
  module GP = UnauthorizedOriginPartitionGame(
    BLiveAuthentication(A, B, K, R), S, H
  ).
  module EUFOP = PG.MultiUserEUFCMAGame(
    BSignOriginOperationDirect(BLiveAuthentication(A, B, K, R), H), S
  ).
  module EUFFACT = PG.MultiUserEUFCMAGame(
    BSignOriginFactWitness(BLiveAuthentication(A, B, K, R), H), S
  ).
  module COLL = PG.NodeCollisionGame(
    BHashOrigin(BLiveAuthentication(A, B, K, R), S), H
  ).

  (* L0 is partitioned into an authenticated live execution and the exact
     origin-aware unauthorized event raised by Deliverable A.  This is only
     probability algebra after the concrete shared execution above has been
     constructed; the bad event is not a fresh Boolean premise. *)
  lemma live_success_le_authenticated_plus_origin_failure &m :
    Pr[LAG.main() @ &m : res.`lar_live_success] <=
      Pr[LAG.main() @ &m :
        res.`lar_live_success /\ ! res.`lar_authentication_failure] +
      Pr[LAG.main() @ &m : res.`lar_authentication_failure].
  proof.
    have hsub :
      Pr[LAG.main() @ &m : res.`lar_live_success] <=
      Pr[LAG.main() @ &m :
        (res.`lar_live_success /\ ! res.`lar_authentication_failure) \/
         res.`lar_authentication_failure].
    + rewrite Pr [mu_sub]=> /#.
    have hunion :
      Pr[LAG.main() @ &m :
        (res.`lar_live_success /\ ! res.`lar_authentication_failure) \/
         res.`lar_authentication_failure] <=
      Pr[LAG.main() @ &m :
        res.`lar_live_success /\ ! res.`lar_authentication_failure] +
      Pr[LAG.main() @ &m : res.`lar_authentication_failure].
    + rewrite Pr [mu_or].
      smt(ge0_mu).
    smt().
  qed.

  lemma live_authentication_failure_exactly_deliverable_a
      &m :
    Pr[LAG.main() @ &m : res.`lar_authentication_failure] =
    Pr[GP.main(live_auth_initial_state) @ &m : res.`opr_real].
  proof.
    byequiv
      (_ : ={glob A, glob S, glob H, glob B, glob K, glob R} ==>
           res{1}.`lar_authentication_failure = res{2}.`opr_real) => //.
    proc.
    inline LAG.main.
    sim.
  qed.

  (* Exact AuthLoss expansion for the live adversary.  Every nonzero term is
     the named Deliverable A primitive game with the concrete live reduction
     adversary [BLiveAuthentication]; the two factors and the encoding term are the already
     proved Deliverable A constants. *)
  lemma live_authentication_failure_bound &m :
    Pr[LAG.main() @ &m : res.`lar_authentication_failure] <=
        q_operation_signature_factor *
          Pr[EUFOP.main(live_auth_initial_state) @ &m : res]
      + q_fact_signature_factor *
          Pr[EUFFACT.main(live_auth_initial_state) @ &m : res]
      + Pr[COLL.main(live_auth_initial_state) @ &m : res]
      + encoding_failure_probability.
  proof.
    rewrite (live_authentication_failure_exactly_deliverable_a &m).
    exact
      (UnauthorizedOriginFinalBound.adv_unauthorized_origin_bound
        &m live_auth_initial_state).
  qed.
end section LiveAuthenticationHop.
