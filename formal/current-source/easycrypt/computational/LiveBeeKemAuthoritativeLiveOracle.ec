require import AllCore List FSet.
require import ProtocolTypes ProtocolChecks CanonicalEncoding.
require import ProtocolPrimitives AuthorizationState UnauthorizedSignatureReduction.
require import UnauthorizedOriginGame LiveKeyGame.
require import BeeKemTypes BeeKemQueryLog BeeKemKiGame.
require import LiveBeeKemAuthoritativeTypes.
require import LiveBeeKemAuthoritativeApplicationState.
require import LiveBeeKemAuthoritativeApplicationAdapter.
require import LiveBeeKemAuthoritativeLiveTypes.

import PG.

(* Full authenticated application wrapper over the authoritative Figure-8
   oracle.  All BeeKEM control, delivery, reveal, challenge, and compromise
   calls are delegated to [AuthoritativeApplicationBeeKemCore].  This module
   owns only public authorization-label state, derived-output routing, and the
   exact root cache needed to share one KI challenge across PRF domains. *)
module AuthoritativeLiveProtocolOracle(
  Auth : ORIGIN_TRACKED_UNAUTHORIZED_ORACLE,
  O : BEEKEM_KI_ORACLES,
  K : MULTI_DOMAIN_KEY_SCHEDULE
) = {
  module Bee = AuthoritativeApplicationBeeKemOracle(O)

  var public_state : protocol_state
  var current_authorization_digest : authorization_digest
  var roots : authoritative_application_root_cache
  var revealed_live : authoritative_application_mark_store
  var challenged_live : authoritative_application_mark_store
  var derived_queries : live_query list
  var runtime_fault : bool

  proc init(
    users : application_user_registry,
    initial_state : protocol_state,
    initial_digest : authorization_digest
  ) : unit = {
    Bee.init(users, initial_state.`ps_document_id);
    public_state <- initial_state;
    current_authorization_digest <- initial_digest;
    roots <- empty_authoritative_application_root_cache;
    revealed_live <- empty_authoritative_application_mark_store;
    challenged_live <- empty_authoritative_application_mark_store;
    derived_queries <- [];
    runtime_fault <- false;
  }

  proc sign_operation(
    envelope : operation_envelope
  ) : signed_operation = {
    var operation : signed_operation;
    operation <@ Auth.sign_operation(envelope);
    return operation;
  }

  proc sign_authorization_fact(
    fact : authorization_fact
  ) : signed_authorization_fact = {
    var signed_fact : signed_authorization_fact;
    signed_fact <@ Auth.sign_authorization_fact(fact);
    return signed_fact;
  }

  proc create_group(
    creator : principal,
    initial_members : principal fset
  ) : node_id option = {
    var result : node_id option;
    result <@ Bee.create_group(
      creator, initial_members, current_authorization_digest
    );
    return result;
  }

  proc add_member(
    author : principal,
    target : principal
  ) : node_id option = {
    var result : node_id option;
    result <@ Bee.add_member(
      author, target, current_authorization_digest
    );
    return result;
  }

  proc remove_member(
    author : principal,
    target : principal
  ) : node_id option = {
    var result : node_id option;
    result <@ Bee.remove_member(
      author, target, current_authorization_digest
    );
    return result;
  }

  proc send_beekem_update(author : principal) : node_id option = {
    var result : node_id option;
    result <@ Bee.send_update(author, current_authorization_digest);
    return result;
  }

  proc deliver(node : node_id, recipient : principal) : bool = {
    var result : bool;
    result <@ Bee.deliver(node, recipient);
    return result;
  }

  proc acquire_challenge_root(
    member : principal,
    node : node_id
  ) : beekem_secret option = {
    var output : application_beekem_output_result;
    var root : beekem_secret option;

    root <- roots member node;
    if (root = None) {
      output <@ Bee.Core.challenge(member, node);
      root <- application_beekem_output_root output.`abo_secret_output;
      if (output.`abo_runtime_fault) {
        runtime_fault <- true;
      }
      if (output.`abo_canonical_accepted /\ root = None) {
        runtime_fault <- true;
      }
      if (root <> None) {
        roots <- authoritative_application_root_cache_put
          roots member node (oget root);
      }
    }
    return root;
  }

  proc reveal_live_key(
    member : principal,
    node : node_id
  ) : live_application_key option = {
    var root : beekem_secret option;
    var digest : authorization_digest option;
    var label : live_key_label;
    var key : live_application_key;
    var result : live_application_key option;
    var output : application_beekem_output_result;

    root <- None;
    digest <- Bee.Core.digests node;
    label <- witness;
    key <- witness;
    result <- None;

    if (! revealed_live member node /\
        ! challenged_live member node /\ digest <> None) {
      output <@ Bee.Core.reveal(member, node);
      root <- application_beekem_output_root output.`abo_secret_output;
      if (output.`abo_runtime_fault) {
        runtime_fault <- true;
      }
      if (output.`abo_canonical_accepted /\ root = None) {
        runtime_fault <- true;
      }
      if (root <> None) {
        label <- live_label_of public_state node (oget digest);
        key <@ K.derive_live(oget root, label);
        revealed_live <- authoritative_application_mark_store_put
          revealed_live member node true;
        derived_queries <- rcons derived_queries
          {| lq_kind = LiveRevealQuery member;
             lq_operation = Some node |};
        result <- Some key;
      }
    }
    return result;
  }

  proc challenge_live(
    member : principal,
    node : node_id
  ) : live_application_key option = {
    var root : beekem_secret option;
    var digest : authorization_digest option;
    var label : live_key_label;
    var key : live_application_key;
    var result : live_application_key option;

    root <- None;
    digest <- Bee.Core.digests node;
    label <- witness;
    key <- witness;
    result <- None;

    if (! revealed_live member node /\
        ! challenged_live member node /\ digest <> None) {
      root <@ acquire_challenge_root(member, node);
      if (root <> None) {
        label <- live_label_of public_state node (oget digest);
        key <@ K.derive_live(oget root, label);
        challenged_live <- authoritative_application_mark_store_put
          challenged_live member node true;
        derived_queries <- rcons derived_queries
          {| lq_kind = LiveChallengeQuery member;
             lq_operation = Some node |};
        result <- Some key;
      }
    }
    return result;
  }

  proc reveal_history_output(
    member : principal,
    node : node_id,
    segment : segment_id
  ) : history_domain_output option = {
    var root : beekem_secret option;
    var digest : authorization_digest option;
    var label : history_key_label;
    var output : history_domain_output;
    var result : history_domain_output option;

    root <- None;
    digest <- Bee.Core.digests node;
    label <- witness;
    output <- witness;
    result <- None;

    if (digest <> None) {
      root <@ acquire_challenge_root(member, node);
      if (root <> None) {
        label <- history_label_of public_state segment (oget digest);
        output <@ K.derive_history(oget root, label);
        derived_queries <- rcons derived_queries
          {| lq_kind = LiveHistoryOutputQuery member segment;
             lq_operation = Some node |};
        result <- Some output;
      }
    }
    return result;
  }

  proc reveal_history_capability(
    member : principal,
    node : node_id,
    segment : segment_id,
    cover : segment_cover
  ) : history_capability_output option = {
    var root : beekem_secret option;
    var digest : authorization_digest option;
    var label : history_key_label;
    var output : history_capability_output;
    var result : history_capability_output option;

    root <- None;
    digest <- Bee.Core.digests node;
    label <- witness;
    output <- witness;
    result <- None;

    if (digest <> None) {
      root <@ acquire_challenge_root(member, node);
      if (root <> None) {
        label <- history_label_of public_state segment (oget digest);
        output <@ K.derive_history_capability(oget root, label, cover);
        derived_queries <- rcons derived_queries
          {| lq_kind = LiveHistoryCapabilityQuery member segment;
             lq_operation = Some node |};
        result <- Some output;
      }
    }
    return result;
  }

  proc compromise_protocol_state(
    member : principal
  ) : beekem_member_state option = {
    var result : beekem_member_state option;
    result <@ Bee.compromise(member);
    return result;
  }

  proc submit_operation(
    operation : signed_operation,
    view : public_view
  ) : bool = {
    var envelope : operation_envelope option;
    var identifier : operation_id option;
    var accepted : bool;

    envelope <- decode_operation operation.`so_raw;
    identifier <- if envelope = None then None
      else Some (oget envelope).`oe_operation_id;
    accepted <@ Auth.submit(operation, view);
    if (accepted /\ envelope <> None) {
      current_authorization_digest <-
        (oget envelope).`oe_authorization_digest;
    }
    derived_queries <- rcons derived_queries
      {| lq_kind = LiveSubmitOperationQuery identifier accepted;
         lq_operation = None |};
    return accepted;
  }
}.
