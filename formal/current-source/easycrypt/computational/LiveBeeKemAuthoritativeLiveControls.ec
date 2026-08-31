require import AllCore List FSet.
require import ProtocolTypes ProtocolChecks CanonicalEncoding.
require import ProtocolPrimitives AuthorizationState UnauthorizedSignatureReduction.
require import UnauthorizedOriginGame LiveKeyGame.
require import BeeKemTypes BeeKemQueryLog BeeKemSafety BeeKemKiGame.
require import BeeKemGameWitnesses.
require import LiveBeeKemAuthoritativeTypes.
require import LiveBeeKemAuthoritativeApplicationState.
require import LiveBeeKemAuthoritativeApplicationAdapter.
require import LiveBeeKemAuthoritativeRootBridge.
require import LiveBeeKemAuthoritativeLiveTypes.
require import LiveBeeKemAuthoritativeLiveOracle.

import PG.

(* History-first scheduling is the difficult domain-sharing case: the history
   query obtains the KI test root, and the later live challenge consumes the
   same cached root without a second challenge or any local random sampling. *)
op authoritative_live_witness_state : protocol_state =
  {| ps_creator = authoritative_adapter_witness_principal;
     ps_document_id = authoritative_adapter_witness_document;
     ps_nodes = fset0;
     ps_closures = fun _ => None;
     ps_fact_contents = fun _ => None;
     ps_seen_operation_ids = fset0;
     ps_seen_nonces = fset0;
     ps_beekem_paths = fun _ => None;
     ps_history_expectation = None;
     ps_expected_puncture_regions = fset0 |}.

op authoritative_live_witness_digest : authorization_digest =
  AuthorizationDigest 710.

op authoritative_live_witness_segment : segment_id = SegmentId 711.

module AuthoritativeLiveWrapperAuth : ORIGIN_TRACKED_UNAUTHORIZED_ORACLE = {
  proc sign_operation(envelope : operation_envelope) : signed_operation = {
    return witness;
  }

  proc sign_authorization_fact(
    fact : authorization_fact
  ) : signed_authorization_fact = {
    return witness;
  }

  proc submit(
    operation : signed_operation,
    view : public_view
  ) : bool = {
    return false;
  }
}.

module AuthoritativeLiveHistoryFirstState = {
  var root : beekem_secret option
  var attempts : application_beekem_attempt_log
  var forwarded_count : int
  var runtime_fault : bool
}.

module AuthoritativeLiveHistoryFirstWitness(O : BEEKEM_KI_ORACLES) = {
  module Live = AuthoritativeLiveProtocolOracle(
    AuthoritativeLiveWrapperAuth,
    O,
    TestMultiDomainKeySchedule
  )

  proc attack() : bool = {
    var created : node_id option;
    var updated : node_id option;
    var history : history_domain_output option;
    var live : live_application_key option;

    Live.init(
      authoritative_adapter_witness_registry,
      authoritative_live_witness_state,
      authoritative_live_witness_digest
    );
    created <@ Live.create_group(
      authoritative_adapter_witness_principal,
      fset0
    );
    updated <@ Live.send_beekem_update(
      authoritative_adapter_witness_principal
    );
    history <@ Live.reveal_history_output(
      authoritative_adapter_witness_principal,
      NodeId 2,
      authoritative_live_witness_segment
    );
    live <@ Live.challenge_live(
      authoritative_adapter_witness_principal,
      NodeId 2
    );
    AuthoritativeLiveHistoryFirstState.root <-
      Live.roots authoritative_adapter_witness_principal (NodeId 2);
    AuthoritativeLiveHistoryFirstState.attempts <-
      Live.Bee.Core.attempts;
    AuthoritativeLiveHistoryFirstState.forwarded_count <-
      Live.Bee.Core.forwarded_count;
    AuthoritativeLiveHistoryFirstState.runtime_fault <-
      Live.runtime_fault \/ Live.Bee.Core.runtime_fault;

    return
         created = Some (NodeId 1)
      /\ updated = Some (NodeId 2)
      /\ history <> None
      /\ live <> None
      /\ AuthoritativeLiveHistoryFirstState.root =
           Some (BeeKemSecret 2)
      /\ size Live.derived_queries = 2
      /\ ! AuthoritativeLiveHistoryFirstState.runtime_fault;
  }
}.

module AuthoritativeLiveHistoryFirstGame =
  BeeKemKiGame(
    AuthoritativeLiveHistoryFirstWitness,
    BeeKemWitnessProtocol
  ).

lemma authoritative_live_history_first_uses_one_exact_challenge :
  hoare [AuthoritativeLiveHistoryFirstGame.main_with_fixed_bit :
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
    /\ AuthoritativeLiveHistoryFirstState.root = Some (BeeKemSecret 2)
    /\ AuthoritativeLiveHistoryFirstState.forwarded_count = 3
    /\ size AuthoritativeLiveHistoryFirstState.attempts = 3
    /\ ! AuthoritativeLiveHistoryFirstState.runtime_fault].
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
    /authoritative_live_witness_state /authoritative_adapter_witness_document
    /authoritative_adapter_witness_principal
    /authoritative_live_witness_digest /authoritative_live_witness_segment
    /application_group_of_document
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
    /empty_authoritative_application_root_cache
    /authoritative_application_root_cache_put
    /empty_authoritative_application_mark_store
    /authoritative_application_mark_store_put
    /application_beekem_output_root
    /application_beekem_root_bridge_value
    /application_beekem_root_bridge
    /application_beekem_root_of_authoritative
    /authoritative_application_root_code
    /authoritative_application_root_result_of_beekem
    /authoritative_application_root_of_beekem
    /live_label_of /history_label_of /expected_protocol_version
    /test_live_material /test_history_material
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
