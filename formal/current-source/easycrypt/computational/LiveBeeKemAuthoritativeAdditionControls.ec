require import AllCore List FSet.
require import ProtocolTypes BeeKemTypes BeeKemQueryLog BeeKemProtocol.
require import BeeKemSafety BeeKemKiGame BeeKemGameWitnesses.
require import LiveBeeKemAuthoritativeTypes.
require import LiveBeeKemAuthoritativeApplicationState.
require import LiveBeeKemAuthoritativeApplicationAdapter.
require import LiveBeeKemAuthoritativeQueryBridge.
require import LiveBeeKemAuthoritativeCounterBridge.

op authoritative_application_add_target : principal =
  {| p_verification_key = VerificationKey 711;
     p_incarnation_nonce = IncarnationNonce 1 |}.

op authoritative_application_add_target_user : beekem_user =
  BeeKemUser 711.

op authoritative_application_add_registry : application_user_registry =
  application_user_registry_bind
    authoritative_adapter_witness_registry
    authoritative_application_add_target
    authoritative_application_add_target_user.

op authoritative_application_add_digest : authorization_digest =
  AuthorizationDigest 708.

op authoritative_application_add_query : beekem_query =
  {| bq_id = BeeKemQueryId 2;
     bq_kind = BeeQueryAdd;
     bq_actor = beekem_witness_user;
     bq_target = Some authoritative_application_add_target_user;
     bq_counter = Some (BeeKemCounter 2);
     bq_operation = Some beekem_witness_add_id;
     bq_actor_frontier = fset1 beekem_witness_create_id;
     bq_target_frontier = fset0;
     bq_accepted = true;
     bq_rejection = None |}.

op authoritative_application_add_log : beekem_query_log =
  [ authoritative_query_bridge_create_query;
    authoritative_application_add_query ].

module AuthoritativeApplicationAddState = {
  var attempts : application_beekem_attempt_log
  var forwarded_count : int
  var runtime_fault : bool
}.

module AuthoritativeApplicationAddWitness(O : BEEKEM_KI_ORACLES) = {
  module Adapter = AuthoritativeApplicationBeeKemOracle(O)

  proc attack() : bool = {
    var created : node_id option;
    var added : node_id option;

    AuthoritativeApplicationAddState.attempts <- [];
    AuthoritativeApplicationAddState.forwarded_count <- 0;
    AuthoritativeApplicationAddState.runtime_fault <- true;
    Adapter.init(
      authoritative_application_add_registry,
      authoritative_adapter_witness_document
    );
    created <@ Adapter.create_group(
      authoritative_adapter_witness_principal,
      fset0,
      authoritative_application_add_digest
    );
    added <@ Adapter.add_member(
      authoritative_adapter_witness_principal,
      authoritative_application_add_target,
      authoritative_application_add_digest
    );
    AuthoritativeApplicationAddState.attempts <- Adapter.Core.attempts;
    AuthoritativeApplicationAddState.forwarded_count <-
      Adapter.Core.forwarded_count;
    AuthoritativeApplicationAddState.runtime_fault <- Adapter.Core.runtime_fault;
    return false;
  }
}.

module AuthoritativeApplicationAddGame =
  BeeKemKiGame(
    AuthoritativeApplicationAddWitness,
    BeeKemWitnessProtocol
  ).

(* The application-side accepted Add count and the authoritative game evidence
   are computed independently from the two exact logs and agree at one. *)
lemma authoritative_application_addition_count_bridge_reachable :
  hoare [AuthoritativeApplicationAddGame.main_with_fixed_bit :
       users = [beekem_witness_user]
    /\ group = beekem_witness_group
    /\ kappa = 1
    /\ membership = beekem_witness_membership
    /\ hidden_bit = false
    ==>
       res.`bke_safe
    /\ ! res.`bke_adversary_guess
    /\ res.`bke_challenge_count = 0
    /\ res.`bke_member_addition_count = 1
    /\ res.`bke_win
    /\ AuthoritativeApplicationAddState.forwarded_count = 2
    /\ size AuthoritativeApplicationAddState.attempts = 2
    /\ ! AuthoritativeApplicationAddState.runtime_fault
    /\ AuthoritativeApplicationAddGame.O.Environment.query_log =
         authoritative_application_add_log
    /\ application_beekem_attempts_match_queries_exact
         authoritative_application_add_registry
         AuthoritativeApplicationAddState.attempts
         AuthoritativeApplicationAddGame.O.Environment.query_log
    /\ application_beekem_challenge_count
         AuthoritativeApplicationAddState.attempts =
         res.`bke_challenge_count
    /\ application_beekem_member_addition_count
         AuthoritativeApplicationAddState.attempts =
         res.`bke_member_addition_count].
proof.
  proc; inline *.
  do ! (
    (rcondt ^if; first by auto=> />; cbv delta; rewrite ?inE ?elems_fset0 ?elems_fset1; cbv delta; rewrite ?inE ?elems_fset0 ?elems_fset1; cbv delta) ||
    (rcondf ^if; first by auto=> />; cbv delta; rewrite ?inE ?elems_fset0 ?elems_fset1; cbv delta; rewrite ?inE ?elems_fset0 ?elems_fset1; cbv delta) ||
    (rcondt ^while; first by auto=> />; cbv delta; rewrite ?inE ?elems_fset0 ?elems_fset1; cbv delta; rewrite ?inE ?elems_fset0 ?elems_fset1; cbv delta) ||
    (rcondf ^while; first by auto=> />; cbv delta; rewrite ?inE ?elems_fset0 ?elems_fset1; cbv delta; rewrite ?inE ?elems_fset0 ?elems_fset1; cbv delta)).
  by auto=> />; cbv delta; rewrite ?inE ?elems_fset0 ?elems_fset1; cbv delta; rewrite ?inE ?elems_fset0 ?elems_fset1; cbv delta; rewrite ?inE ?elems_fset0 ?elems_fset1; cbv delta.
qed.
