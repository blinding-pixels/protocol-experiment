require import AllCore List FSet.
require import ProtocolTypes BeeKemTypes BeeKemQueryLog BeeKemSafety BeeKemKiGame.
require import BeeKemGameWitnesses.
require import LiveBeeKemAuthoritativeTypes.
require import LiveBeeKemAuthoritativeApplicationState.
require import LiveBeeKemAuthoritativeApplicationAdapter.

op authoritative_application_adapter_digest : authorization_digest =
  AuthorizationDigest 705.

(* Export proof-only observations through a separate module.  The KI game
   ascribes its adversary to [BEEKEM_KI_ADVERSARY], so implementation-only
   nested modules are intentionally hidden at the game boundary. *)
module AuthoritativeApplicationAdapterWitnessState = {
  var forwarded_count : int
  var attempt_count : int
  var runtime_fault : bool
}.

module AuthoritativeApplicationAdapterWitness(
  O : BEEKEM_KI_ORACLES
) = {
  module Adapter = AuthoritativeApplicationBeeKemOracle(O)

  var created : node_id option
  var updated : node_id option
  var challenged : authoritative_application_root_result option

  proc attack() : bool = {
    AuthoritativeApplicationAdapterWitnessState.forwarded_count <- 0;
    AuthoritativeApplicationAdapterWitnessState.attempt_count <- 0;
    AuthoritativeApplicationAdapterWitnessState.runtime_fault <- true;
    Adapter.init(
      authoritative_adapter_witness_registry,
      authoritative_adapter_witness_document
    );
    created <@ Adapter.create_group(
      authoritative_adapter_witness_principal,
      fset0,
      authoritative_application_adapter_digest
    );
    updated <@ Adapter.send_update(
      authoritative_adapter_witness_principal,
      authoritative_application_adapter_digest
    );
    challenged <@ Adapter.challenge(
      authoritative_adapter_witness_principal,
      NodeId 2
    );
    AuthoritativeApplicationAdapterWitnessState.forwarded_count <-
      Adapter.Core.forwarded_count;
    AuthoritativeApplicationAdapterWitnessState.attempt_count <-
      size Adapter.Core.attempts;
    AuthoritativeApplicationAdapterWitnessState.runtime_fault <-
      Adapter.Core.runtime_fault;
    return
         created = Some (NodeId 1)
      /\ updated = Some (NodeId 2)
      /\ challenged = Some
           (AuthoritativeRootValue (AuthoritativeApplicationRoot [true]));
  }
}.

module AuthoritativeApplicationAdapterWitnessGame =
  BeeKemKiGame(
    AuthoritativeApplicationAdapterWitness,
    BeeKemWitnessProtocol
  ).

(* The exact canonical Create -> Update -> Challenge trace reaches the
   application adapter, establishes two collision-free node addresses, forwards
   exactly three canonical queries, and consumes the authoritative real branch.
   The challenge root is returned only through the application wrapper. *)
lemma authoritative_application_adapter_real_branch_reachable :
  hoare [AuthoritativeApplicationAdapterWitnessGame.main_with_fixed_bit :
       users = [beekem_witness_user]
    /\ group = beekem_witness_group
    /\ kappa = 1
    /\ membership = beekem_witness_membership
    /\ hidden_bit = true
    ==>
       res.`bke_hidden_bit
    /\ res.`bke_adversary_guess
    /\ res.`bke_safe
    /\ ! res.`bke_protocol_consistency_failure
    /\ res.`bke_challenge_count = 1
    /\ res.`bke_member_addition_count = 0
    /\ res.`bke_real_branch_count = 1
    /\ res.`bke_random_branch_count = 0
    /\ res.`bke_random_sample_count = 0
    /\ res.`bke_win
    /\ AuthoritativeApplicationAdapterWitnessState.forwarded_count = 3
    /\ AuthoritativeApplicationAdapterWitnessState.attempt_count = 3
    /\ ! AuthoritativeApplicationAdapterWitnessState.runtime_fault].
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
    /authoritative_application_adapter_digest
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
