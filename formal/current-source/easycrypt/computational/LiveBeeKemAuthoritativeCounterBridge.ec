require import AllCore List FSet.
require import ProtocolTypes BeeKemTypes BeeKemQueryLog BeeKemProtocol.
require import BeeKemSafety BeeKemKiGame BeeKemGameWitnesses.
require import LiveBeeKemAuthoritativeTypes.
require import LiveBeeKemAuthoritativeApplicationState.
require import LiveBeeKemAuthoritativeApplicationAdapter.
require import LiveBeeKemAuthoritativeQueryBridge.

(* Application-side counters are computed only from forwarded, canonically
   accepted attempts.  Create contributes its actual initial-member cardinality;
   Add contributes one; rejected and locally rejected attempts contribute zero. *)
op application_beekem_member_addition_delta
    (kind : application_beekem_attempt_kind)
    (forwarded accepted : bool) : int =
  if ! forwarded \/ ! accepted then 0
  else
    with kind = ApplicationBeeKemCreateAttempt payload =>
      size (elems payload.`2)
    with kind = ApplicationBeeKemAddAttempt payload => 1
    with kind = _ => 0.

op application_beekem_member_addition_count
    (attempts : application_beekem_attempt_log) : int =
  with attempts = [] => 0
  with attempts = attempt :: rest =>
    application_beekem_member_addition_delta
      attempt.`aba_kind attempt.`aba_forwarded
      attempt.`aba_canonical_accepted
    + application_beekem_member_addition_count rest.

op application_beekem_challenge_delta
    (kind : application_beekem_attempt_kind)
    (forwarded accepted : bool) : int =
  if ! forwarded \/ ! accepted then 0
  else
    with kind = ApplicationBeeKemChallengeAttempt payload => 1
    with kind = _ => 0.

op application_beekem_challenge_count
    (attempts : application_beekem_attempt_log) : int =
  with attempts = [] => 0
  with attempts = attempt :: rest =>
    application_beekem_challenge_delta
      attempt.`aba_kind attempt.`aba_forwarded
      attempt.`aba_canonical_accepted
    + application_beekem_challenge_count rest.

op authoritative_rejected_create_digest : authorization_digest =
  AuthorizationDigest 707.

op authoritative_rejected_create_query : beekem_query =
  {| bq_id = BeeKemQueryId 2;
     bq_kind = BeeQueryCreate;
     bq_actor = beekem_witness_user;
     bq_target = None;
     bq_counter = None;
     bq_operation = None;
     bq_actor_frontier = fset1 beekem_witness_create_id;
     bq_target_frontier = fset0;
     bq_accepted = false;
     bq_rejection = Some BeeRejectAlreadyCreated |}.

op authoritative_rejected_create_log : beekem_query_log =
  [ authoritative_query_bridge_create_query;
    authoritative_rejected_create_query ].

module AuthoritativeRejectedCreateState = {
  var attempts : application_beekem_attempt_log
  var forwarded_count : int
  var runtime_fault : bool
}.

module AuthoritativeRejectedCreateWitness(O : BEEKEM_KI_ORACLES) = {
  module Adapter = AuthoritativeApplicationBeeKemOracle(O)

  proc attack() : bool = {
    var first : node_id option;
    var second : node_id option;

    AuthoritativeRejectedCreateState.attempts <- [];
    AuthoritativeRejectedCreateState.forwarded_count <- 0;
    AuthoritativeRejectedCreateState.runtime_fault <- true;
    Adapter.init(
      authoritative_adapter_witness_registry,
      authoritative_adapter_witness_document
    );
    first <@ Adapter.create_group(
      authoritative_adapter_witness_principal,
      fset0,
      authoritative_rejected_create_digest
    );
    second <@ Adapter.create_group(
      authoritative_adapter_witness_principal,
      fset0,
      authoritative_rejected_create_digest
    );
    AuthoritativeRejectedCreateState.attempts <- Adapter.Core.attempts;
    AuthoritativeRejectedCreateState.forwarded_count <-
      Adapter.Core.forwarded_count;
    AuthoritativeRejectedCreateState.runtime_fault <-
      Adapter.Core.runtime_fault;
    return first = Some (NodeId 1) /\ second = None;
  }
}.

module AuthoritativeRejectedCreateGame =
  BeeKemKiGame(
    AuthoritativeRejectedCreateWitness,
    BeeKemWitnessProtocol
  ).

(* A canonical rejection remains present on both sides of the adapter bridge.
   In particular, the second Create consumes query id 2 and records the exact
   authoritative [BeeRejectAlreadyCreated] reason; it is not filtered out as an
   unsuccessful query. *)
lemma authoritative_rejected_create_is_retained_exactly :
  hoare [AuthoritativeRejectedCreateGame.main_with_fixed_bit :
       users = [beekem_witness_user]
    /\ group = beekem_witness_group
    /\ kappa = 1
    /\ membership = beekem_witness_membership
    /\ hidden_bit = true
    ==>
       res.`bke_safe
    /\ res.`bke_adversary_guess
    /\ res.`bke_challenge_count = 0
    /\ res.`bke_member_addition_count = 0
    /\ res.`bke_win
    /\ AuthoritativeRejectedCreateState.forwarded_count = 2
    /\ size AuthoritativeRejectedCreateState.attempts = 2
    /\ ! AuthoritativeRejectedCreateState.runtime_fault
    /\ AuthoritativeRejectedCreateGame.O.Environment.query_log =
         authoritative_rejected_create_log
    /\ application_beekem_attempts_match_queries_exact
         authoritative_adapter_witness_registry
         AuthoritativeRejectedCreateState.attempts
         AuthoritativeRejectedCreateGame.O.Environment.query_log
    /\ application_beekem_challenge_count
         AuthoritativeRejectedCreateState.attempts =
         res.`bke_challenge_count
    /\ application_beekem_member_addition_count
         AuthoritativeRejectedCreateState.attempts =
         res.`bke_member_addition_count].
proof.
  proc.
  inline *.
  rcondt ^while; first by auto.
  rcondf ^while; first by auto.
  rcondf ^while; first by auto.
  auto.
  rewrite /authoritative_adapter_witness_registry
    /application_user_registry_bind /empty_application_user_registry
    /authoritative_adapter_witness_document /application_group_of_document
    /authoritative_adapter_witness_principal
    /authoritative_rejected_create_digest
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
    /authoritative_rejected_create_log
    /authoritative_rejected_create_query
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
    /application_beekem_member_addition_count
    /application_beekem_member_addition_delta
    /beekem_witness_membership /beekem_witness_initial_member_state
    /beekem_member_retention_valid /beekem_witness_personal_secret
    /beekem_witness_after_create /beekem_witness_control
    /beekem_witness_create_operation /beekem_witness_operation
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
