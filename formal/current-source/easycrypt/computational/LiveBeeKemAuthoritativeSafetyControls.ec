require import AllCore List FSet.
require import ProtocolTypes BeeKemTypes BeeKemQueryLog BeeKemProtocol.
require import BeeKemSafety BeeKemKiGame BeeKemGameWitnesses.
require import LiveBeeKemAuthoritativeTypes.
require import LiveBeeKemAuthoritativeApplicationState.
require import LiveBeeKemAuthoritativeApplicationAdapter.
require import LiveBeeKemAuthoritativeQueryBridge.
require import LiveBeeKemAuthoritativeCounterBridge.

op authoritative_application_unsafe_digest : authorization_digest =
  AuthorizationDigest 709.

op authoritative_application_compromise_query : beekem_query =
  {| bq_id = BeeKemQueryId 4;
     bq_kind = BeeQueryCompromise;
     bq_actor = beekem_witness_user;
     bq_target = None;
     bq_counter = None;
     bq_operation = None;
     bq_actor_frontier = fset1 beekem_witness_update_id;
     bq_target_frontier = fset0;
     bq_accepted = true;
     bq_rejection = None |}.

op authoritative_application_unsafe_log : beekem_query_log =
  [ authoritative_query_bridge_create_query;
    authoritative_query_bridge_update_query;
    authoritative_query_bridge_challenge_query;
    authoritative_application_compromise_query ].

module AuthoritativeApplicationUnsafeState = {
  var attempts : application_beekem_attempt_log
  var forwarded_count : int
  var compromise_frontier : beekem_operation_id fset
  var runtime_fault : bool
}.

module AuthoritativeApplicationUnsafeWitness(O : BEEKEM_KI_ORACLES) = {
  module Adapter = AuthoritativeApplicationBeeKemOracle(O)

  proc attack() : bool = {
    var created : node_id option;
    var updated : node_id option;
    var challenged : authoritative_application_root_result option;
    var compromised : beekem_member_state option;

    AuthoritativeApplicationUnsafeState.attempts <- [];
    AuthoritativeApplicationUnsafeState.forwarded_count <- 0;
    AuthoritativeApplicationUnsafeState.compromise_frontier <- fset0;
    AuthoritativeApplicationUnsafeState.runtime_fault <- true;
    Adapter.init(
      authoritative_adapter_witness_registry,
      authoritative_adapter_witness_document
    );
    created <@ Adapter.create_group(
      authoritative_adapter_witness_principal,
      fset0,
      authoritative_application_unsafe_digest
    );
    updated <@ Adapter.send_update(
      authoritative_adapter_witness_principal,
      authoritative_application_unsafe_digest
    );
    challenged <@ Adapter.challenge(
      authoritative_adapter_witness_principal,
      NodeId 2
    );
    compromised <@ Adapter.compromise(
      authoritative_adapter_witness_principal
    );
    AuthoritativeApplicationUnsafeState.attempts <- Adapter.Core.attempts;
    AuthoritativeApplicationUnsafeState.forwarded_count <-
      Adapter.Core.forwarded_count;
    AuthoritativeApplicationUnsafeState.compromise_frontier <-
      if compromised = None then fset0 else (oget compromised).`bms_frontier;
    AuthoritativeApplicationUnsafeState.runtime_fault <- Adapter.Core.runtime_fault;
    return
         created = Some (NodeId 1)
      /\ updated = Some (NodeId 2)
      /\ challenged = Some
           (AuthoritativeRootValue (AuthoritativeApplicationRoot [true]))
      /\ compromised <> None;
  }
}.

module AuthoritativeApplicationUnsafeGame =
  BeeKemKiGame(
    AuthoritativeApplicationUnsafeWitness,
    BeeKemWitnessProtocol
  ).

(* Create -> Update -> Challenge -> immediate snapshot compromise is executable
   through the application adapter but is rejected by the exact authoritative
   safety predicate.  The challenge remains counted exactly once, and the
   compromise frontier copied into the attempt log is the challenger snapshot. *)
lemma authoritative_application_immediate_compromise_is_exactly_unsafe :
  hoare [AuthoritativeApplicationUnsafeGame.main_with_fixed_bit :
       users = [beekem_witness_user]
    /\ group = beekem_witness_group
    /\ kappa = 1
    /\ membership = beekem_witness_membership
    /\ hidden_bit = true
    ==>
       res.`bke_challenge_count = 1
    /\ res.`bke_member_addition_count = 0
    /\ ! res.`bke_safe
    /\ ! res.`bke_win
    /\ AuthoritativeApplicationUnsafeState.forwarded_count = 4
    /\ size AuthoritativeApplicationUnsafeState.attempts = 4
    /\ AuthoritativeApplicationUnsafeState.compromise_frontier =
         fset1 beekem_witness_update_id
    /\ ! AuthoritativeApplicationUnsafeState.runtime_fault
    /\ AuthoritativeApplicationUnsafeGame.O.Environment.query_log =
         authoritative_application_unsafe_log
    /\ application_beekem_attempts_match_queries_exact
         authoritative_adapter_witness_registry
         AuthoritativeApplicationUnsafeState.attempts
         AuthoritativeApplicationUnsafeGame.O.Environment.query_log
    /\ application_beekem_challenge_count
         AuthoritativeApplicationUnsafeState.attempts =
         res.`bke_challenge_count
    /\ application_beekem_member_addition_count
         AuthoritativeApplicationUnsafeState.attempts =
         res.`bke_member_addition_count].
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
    /authoritative_application_unsafe_digest
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
    /authoritative_application_unsafe_log
    /authoritative_application_compromise_query
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
    /application_beekem_challenge_count
    /application_beekem_challenge_delta
    /application_beekem_challenge_kind_delta
    /application_beekem_member_addition_count
    /application_beekem_member_addition_delta
    /application_beekem_member_addition_kind_delta
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
    /beekem_challenge_safe_against /beekem_challenge_compromise_pair_safe
    /beekem_kappa_fsu_clause /beekem_pcs_clause /beekem_kappa_cfs_clause
    /beekem_update_chain_between /beekem_update_chain_ending_at
    /beekem_successful_update_for /beekem_q2op_precedes
    /beekem_q2op_precedes_or_equals /beekem_q2op_concurrent
    /beekem_q2op_set /beekem_ids_precede_frontier
    /beekem_ids_precede_or_equal_frontier /beekem_id_precedes_some
    /beekem_id_precedes_or_equals_some /beekem_ids_pairwise_concurrent
    /beekem_id_concurrent_with_all /beekem_operation_ids_concurrent
    /beekem_operation_id_precedes /beekem_operation_id_precedes_or_equals
    /beekem_operation_id_known /beekem_query_successful
    /beekem_query_is_send_update /beekem_query_is_challenge
    /beekem_query_is_compromise /beekem_ki_final_win.
  rewrite (elems_fset1 beekem_witness_create_id)
    (elems_fset1 beekem_witness_update_id).
  smt(in_fset0 in_fset1 size_rcons size_ge0).
qed.
