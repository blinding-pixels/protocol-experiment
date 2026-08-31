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
  proc.
  inline *.
  rcondt ^while; first by auto.
  rcondf ^while; first by auto.
  rcondf ^while; first by auto.
  rcondt ^while; first by auto.
  rcondf ^while; first by auto.
  rcondf ^while; first by auto.
  auto.
  rewrite /authoritative_application_add_registry
    /authoritative_adapter_witness_registry
    /application_user_registry_bind /empty_application_user_registry
    /authoritative_application_add_target
    /authoritative_application_add_target_user
    /authoritative_adapter_witness_document /application_group_of_document
    /authoritative_adapter_witness_principal
    /authoritative_application_add_digest
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
    /authoritative_application_add_log
    /authoritative_application_add_query
    /authoritative_query_bridge_create_query
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
    /beekem_witness_after_create /beekem_witness_after_add
    /beekem_witness_control /beekem_witness_create_operation
    /beekem_witness_add_operation /beekem_witness_operation
    /beekem_control_operation_id /beekem_control_operation
    /beekem_counter_value /beekem_empty_protocol_state
    /beekem_secret_output_is_undefined /beekem_secret_output_is_value
    /beekem_operation_precedes_or_equals /beekem_operation_precedes
    /bee_safe_kappa /beekem_all_challenges_safe
    /beekem_challenge_safe_against /beekem_query_successful
    /beekem_query_is_challenge /beekem_query_is_compromise
    /beekem_ki_final_win.
  smt(in_fset0 in_fset1 size_rcons size_ge0).
qed.
