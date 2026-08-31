require import AllCore List FSet.
require import ProtocolTypes BeeKemTypes BeeKemQueryLog BeeKemSafety BeeKemKiGame.
require import BeeKemGameWitnesses.
require import LiveBeeKemAuthoritativeTypes.
require import LiveBeeKemAuthoritativeApplicationState.
require import LiveBeeKemAuthoritativeApplicationAdapter.

(* Exact application-attempt to authoritative-query correspondence.  Locally
   rejected application requests consume no authoritative query.  Every
   forwarded request consumes one query, in order, and identifies its canonical
   actor, target, message address, acceptance bit, rejection state, and output
   representation.  Causal frontiers remain the full values recorded by the
   authoritative challenger; the adapter never replaces them with a head. *)
op application_beekem_attempt_address_matches_query
    (attempt : application_beekem_attempt)
    (query : beekem_query) : bool =
  if attempt.`aba_address = None
  then query.`bq_counter = None /\ query.`bq_operation = None
  else
       attempt.`aba_node = Some (oget attempt.`aba_address).`aba_node
    /\ query.`bq_counter = Some (oget attempt.`aba_address).`aba_counter
    /\ query.`bq_operation = Some (oget attempt.`aba_address).`aba_operation.

op application_beekem_attempt_control_matches_query
    (attempt : application_beekem_attempt)
    (query : beekem_query) : bool =
  if attempt.`aba_control = None
  then true
  else query.`bq_operation = Some
    (oget attempt.`aba_control).`bgm_operation.`bo_id.

op application_beekem_attempt_kind_matches_query_for
    (registry : application_user_registry)
    (kind : application_beekem_attempt_kind)
    (attempt : application_beekem_attempt)
    (query : beekem_query) : bool =
  with kind = ApplicationBeeKemCreateAttempt (actor, initial_members) =>
         query.`bq_kind = BeeQueryCreate
      /\ registry.`aur_user_of actor = Some query.`bq_actor
      /\ query.`bq_target = None
      /\ query.`bq_target_frontier = fset0
  with kind = ApplicationBeeKemAddAttempt (actor, target) =>
         query.`bq_kind = BeeQueryAdd
      /\ registry.`aur_user_of actor = Some query.`bq_actor
      /\ registry.`aur_user_of target = query.`bq_target
  with kind = ApplicationBeeKemRemoveAttempt (actor, target) =>
         query.`bq_kind = BeeQueryRemove
      /\ registry.`aur_user_of actor = Some query.`bq_actor
      /\ registry.`aur_user_of target = query.`bq_target
  with kind = ApplicationBeeKemUpdateAttempt actor =>
         query.`bq_kind = BeeQuerySendUpdate
      /\ registry.`aur_user_of actor = Some query.`bq_actor
      /\ query.`bq_target = None
      /\ query.`bq_target_frontier = fset0
  with kind = ApplicationBeeKemDeliverAttempt (node, recipient) =>
         query.`bq_kind = BeeQueryDeliver
      /\ attempt.`aba_address <> None
      /\ attempt.`aba_node = Some node
      /\ (oget attempt.`aba_address).`aba_node = node
      /\ query.`bq_actor = (oget attempt.`aba_address).`aba_user
      /\ registry.`aur_user_of recipient = query.`bq_target
  with kind = ApplicationBeeKemRevealAttempt (member, node) =>
         query.`bq_kind = BeeQueryReveal
      /\ registry.`aur_user_of member <> None
      /\ attempt.`aba_address <> None
      /\ attempt.`aba_node = Some node
      /\ (oget attempt.`aba_address).`aba_node = node
      /\ query.`bq_actor = (oget attempt.`aba_address).`aba_user
      /\ query.`bq_target = None
      /\ query.`bq_target_frontier = fset0
  with kind = ApplicationBeeKemChallengeAttempt (member, node) =>
         query.`bq_kind = BeeQueryChallenge
      /\ registry.`aur_user_of member <> None
      /\ attempt.`aba_address <> None
      /\ attempt.`aba_node = Some node
      /\ (oget attempt.`aba_address).`aba_node = node
      /\ query.`bq_actor = (oget attempt.`aba_address).`aba_user
      /\ query.`bq_target = None
      /\ query.`bq_target_frontier = fset0
  with kind = ApplicationBeeKemCompromiseAttempt member =>
         query.`bq_kind = BeeQueryCompromise
      /\ registry.`aur_user_of member = Some query.`bq_actor
      /\ query.`bq_target = None
      /\ query.`bq_counter = None
      /\ query.`bq_operation = None
      /\ query.`bq_target_frontier = fset0
      /\ attempt.`aba_compromise_frontier = query.`bq_actor_frontier.

op application_beekem_attempt_kind_matches_query
    (registry : application_user_registry)
    (attempt : application_beekem_attempt)
    (query : beekem_query) : bool =
  application_beekem_attempt_kind_matches_query_for
    registry attempt.`aba_kind attempt query.

op application_beekem_attempt_matches_query_exact
    (registry : application_user_registry)
    (attempt : application_beekem_attempt)
    (query : beekem_query) : bool =
     attempt.`aba_forwarded
  /\ attempt.`aba_canonical_query_id = Some query.`bq_id
  /\ attempt.`aba_canonical_accepted = query.`bq_accepted
  /\ (query.`bq_accepted <=> query.`bq_rejection = None)
  /\ attempt.`aba_mapping_rejection = None
  /\ application_beekem_attempt_address_matches_query attempt query
  /\ application_beekem_attempt_control_matches_query attempt query
  /\ application_beekem_attempt_kind_matches_query registry attempt query
  /\ application_beekem_attempt_output_exact attempt.

op application_beekem_attempts_match_queries_exact
    (registry : application_user_registry)
    (attempts : application_beekem_attempt_log)
    (queries : beekem_query_log) : bool =
  with attempts = [] => queries = []
  with attempts = attempt :: rest =>
    if attempt.`aba_forwarded
    then
         queries <> []
      /\ application_beekem_attempt_matches_query_exact
           registry attempt (head witness queries)
      /\ application_beekem_attempts_match_queries_exact
           registry rest (behead queries)
    else
         application_beekem_attempt_is_local_rejection attempt
      /\ application_beekem_attempts_match_queries_exact
           registry rest queries.

op authoritative_query_bridge_digest : authorization_digest =
  AuthorizationDigest 706.

op authoritative_query_bridge_create_query : beekem_query =
  {| bq_id = BeeKemQueryId 1;
     bq_kind = BeeQueryCreate;
     bq_actor = beekem_witness_user;
     bq_target = None;
     bq_counter = Some (BeeKemCounter 1);
     bq_operation = Some beekem_witness_create_id;
     bq_actor_frontier = fset0;
     bq_target_frontier = fset0;
     bq_accepted = true;
     bq_rejection = None |}.

op authoritative_query_bridge_update_query : beekem_query =
  {| bq_id = BeeKemQueryId 2;
     bq_kind = BeeQuerySendUpdate;
     bq_actor = beekem_witness_user;
     bq_target = None;
     bq_counter = Some (BeeKemCounter 2);
     bq_operation = Some beekem_witness_update_id;
     bq_actor_frontier = fset1 beekem_witness_create_id;
     bq_target_frontier = fset0;
     bq_accepted = true;
     bq_rejection = None |}.

op authoritative_query_bridge_challenge_query : beekem_query =
  {| bq_id = BeeKemQueryId 3;
     bq_kind = BeeQueryChallenge;
     bq_actor = beekem_witness_user;
     bq_target = None;
     bq_counter = Some (BeeKemCounter 2);
     bq_operation = Some beekem_witness_update_id;
     bq_actor_frontier = fset1 beekem_witness_update_id;
     bq_target_frontier = fset0;
     bq_accepted = true;
     bq_rejection = None |}.

op authoritative_query_bridge_expected_log : beekem_query_log =
  [ authoritative_query_bridge_create_query;
    authoritative_query_bridge_update_query;
    authoritative_query_bridge_challenge_query ].

module AuthoritativeQueryBridgeWitnessState = {
  var attempts : application_beekem_attempt_log
  var forwarded_count : int
  var runtime_fault : bool
}.

module AuthoritativeQueryBridgeWitness(O : BEEKEM_KI_ORACLES) = {
  module Adapter = AuthoritativeApplicationBeeKemOracle(O)

  proc attack() : bool = {
    var created : node_id option;
    var updated : node_id option;
    var challenged : authoritative_application_root_result option;

    AuthoritativeQueryBridgeWitnessState.attempts <- [];
    AuthoritativeQueryBridgeWitnessState.forwarded_count <- 0;
    AuthoritativeQueryBridgeWitnessState.runtime_fault <- true;
    Adapter.init(
      authoritative_adapter_witness_registry,
      authoritative_adapter_witness_document
    );
    created <@ Adapter.create_group(
      authoritative_adapter_witness_principal,
      fset0,
      authoritative_query_bridge_digest
    );
    updated <@ Adapter.send_update(
      authoritative_adapter_witness_principal,
      authoritative_query_bridge_digest
    );
    challenged <@ Adapter.challenge(
      authoritative_adapter_witness_principal,
      NodeId 2
    );
    AuthoritativeQueryBridgeWitnessState.attempts <- Adapter.Core.attempts;
    AuthoritativeQueryBridgeWitnessState.forwarded_count <-
      Adapter.Core.forwarded_count;
    AuthoritativeQueryBridgeWitnessState.runtime_fault <-
      Adapter.Core.runtime_fault;
    return
         created = Some (NodeId 1)
      /\ updated = Some (NodeId 2)
      /\ challenged = Some
           (AuthoritativeRootValue (AuthoritativeApplicationRoot [true]));
  }
}.

module AuthoritativeQueryBridgeWitnessGame =
  BeeKemKiGame(
    AuthoritativeQueryBridgeWitness,
    BeeKemWitnessProtocol
  ).

(* This witness is deliberately stronger than an honest-path reachability
   check: it exposes the exact canonical query records, including all causal
   frontier fields, and proves the adapter's ordered attempt log corresponds to
   them entry by entry. *)
lemma authoritative_application_query_log_bridge_reachable :
  hoare [AuthoritativeQueryBridgeWitnessGame.main_with_fixed_bit :
       users = [beekem_witness_user]
    /\ group = beekem_witness_group
    /\ kappa = 1
    /\ membership = beekem_witness_membership
    /\ hidden_bit = true
    ==>
       res.`bke_safe
    /\ res.`bke_challenge_count = 1
    /\ res.`bke_member_addition_count = 0
    /\ AuthoritativeQueryBridgeWitnessState.forwarded_count = 3
    /\ size AuthoritativeQueryBridgeWitnessState.attempts = 3
    /\ ! AuthoritativeQueryBridgeWitnessState.runtime_fault
    /\ AuthoritativeQueryBridgeWitnessGame.O.Environment.query_log =
         authoritative_query_bridge_expected_log
    /\ application_beekem_attempts_match_queries_exact
         authoritative_adapter_witness_registry
         AuthoritativeQueryBridgeWitnessState.attempts
         AuthoritativeQueryBridgeWitnessGame.O.Environment.query_log].
proof.
  proc.
  inline *.
  rcondt ^while; first by auto.
  rcondf ^while; first by auto.
  rcondf ^while; first by auto.
  rcondt ^while; first by auto.
  rcondf ^while; first by auto.
  rcondf ^while; first by auto.
  auto.
  rewrite /authoritative_adapter_witness_registry
    /application_user_registry_bind /empty_application_user_registry
    /authoritative_adapter_witness_document /application_group_of_document
    /authoritative_adapter_witness_principal
    /authoritative_query_bridge_digest
    /application_beekem_users_of_set /application_beekem_users_of_list
    /LiveBeeKemAuthoritativeTypes.oflist
    /application_beekem_next_query_id
    /empty_application_beekem_counter_store
    /empty_application_beekem_digest_store
    /empty_application_beekem_delivery_store
    /empty_application_beekem_address_registry
    /application_beekem_counter_store_put
    /application_beekem_digest_store_put
     /application_beekem_delivery_store_put
    /application_beekem_address_of_control
     /application_beekem_address_fresh
     /application_beekem_address_registry_bind
    /authoritative_application_root_result_of_beekem
    /authoritative_application_root_of_beekem
    /authoritative_query_bridge_expected_log
    /authoritative_query_bridge_create_query
    /authoritative_query_bridge_update_query
    /authoritative_query_bridge_challenge_query
    /application_beekem_attempts_match_queries_exact
    /application_beekem_attempt_matches_query_exact
    /application_beekem_attempt_address_matches_query
    /application_beekem_attempt_control_matches_query
    /application_beekem_attempt_kind_matches_query
    /application_beekem_attempt_kind_matches_query_for
    /application_beekem_attempt_output_exact
    /application_beekem_output_mapping_exact
    /beekem_witness_membership /beekem_witness_initial_member_state
    /beekem_member_retention_valid /beekem_witness_personal_secret
    /beekem_witness_after_create /beekem_witness_after_update
    /beekem_witness_control /beekem_witness_create_operation
    /beekem_witness_update_operation /beekem_witness_operation
    /beekem_control_operation_id /beekem_control_operation
    /beekem_counter_value /beekem_empty_protocol_state
    /beekem_secret_output_is_undefined /beekem_secret_output_is_value
    /beekem_secret_output_value /beekem_operation_precedes_or_equals
    /beekem_operation_precedes /bee_safe_kappa /beekem_all_challenges_safe
    /beekem_challenge_safe_against /beekem_query_successful
    /beekem_query_is_challenge /beekem_query_is_compromise.
  smt(in_fset0 in_fset1 size_rcons size_ge0).
qed.
