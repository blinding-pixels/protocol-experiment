require import AllCore List FSet.
require import ProtocolTypes ProtocolPrimitives UnauthorizedSignatureReduction.
require import UnauthorizedOriginGame LiveKeyGame LiveBeeKemControl.
require LiveBeeKemKiInterface.
clone import LiveBeeKemKiInterface as BKI.

import PG.

(* Derived-output half of the application simulation.  All live, history, and
   constrained-history values at one (member,node) pair use the same cached
   primitive test root.  No raw BeeKEM secret is returned. *)
module KiBackedDerived(
  Auth : ORIGIN_TRACKED_UNAUTHORIZED_ORACLE,
  O : BKI.BEEKEM_KI_ORACLE,
  K : MULTI_DOMAIN_KEY_SCHEDULE,
  R : LIVE_KEY_SAMPLER
) = {
  module Base = KiBackedControl(Auth, O, K, R)

  var hidden_bit : bool
  var queries : live_query list
  var revealed_live_nodes : node_id fset
  var challenged_live_nodes : node_id fset

  proc init(
    initial_state : protocol_state,
    retention_kappa : int,
    challenge_bit : bool,
    initial_digest : authorization_digest
  ) : unit = {
    Base.init(initial_state, retention_kappa, challenge_bit, initial_digest);
    hidden_bit <- challenge_bit;
    queries <- [];
    revealed_live_nodes <- fset0;
    challenged_live_nodes <- fset0;
  }

  proc record(query : live_query) : unit = {
    queries <- rcons queries query;
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

    root <- None;
    digest <- Base.Core.node_digests node;
    label <- witness;
    key <- witness;
    result <- None;

    if (Base.Core.delivered member node /\ digest <> None /\
        node \notin revealed_live_nodes /\
        node \notin challenged_live_nodes) {
      root <@ Base.root_for(member, node);
      if (root <> None) {
        label <- live_label_of Base.Core.public_state node (oget digest);
        key <@ K.derive_live(oget root, label);
        revealed_live_nodes <- revealed_live_nodes `|` fset1 node;
        queries <- rcons queries
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
    var real_key : live_application_key;
    var random_key : live_application_key;
    var result : live_application_key option;

    root <- None;
    digest <- Base.Core.node_digests node;
    label <- witness;
    real_key <- witness;
    random_key <- witness;
    result <- None;

    if (Base.Core.delivered member node /\ digest <> None /\
        node \notin revealed_live_nodes /\
        node \notin challenged_live_nodes) {
      root <@ Base.root_for(member, node);
      if (root <> None) {
        label <- live_label_of Base.Core.public_state node (oget digest);
        real_key <@ K.derive_live(oget root, label);
        random_key <@ R.sample(label);
        result <- Some (if hidden_bit then real_key else random_key);
        challenged_live_nodes <- challenged_live_nodes `|` fset1 node;
        queries <- rcons queries
          {| lq_kind = LiveChallengeQuery member;
             lq_operation = Some node |};
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
    digest <- Base.Core.node_digests node;
    label <- witness;
    output <- witness;
    result <- None;

    if (Base.Core.delivered member node /\ digest <> None) {
      root <@ Base.root_for(member, node);
      if (root <> None) {
        label <- history_label_of Base.Core.public_state segment (oget digest);
        output <@ K.derive_history(oget root, label);
        queries <- rcons queries
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
    digest <- Base.Core.node_digests node;
    label <- witness;
    output <- witness;
    result <- None;

    if (Base.Core.delivered member node /\ digest <> None) {
      root <@ Base.root_for(member, node);
      if (root <> None) {
        label <- history_label_of Base.Core.public_state segment (oget digest);
        output <@ K.derive_history_capability(oget root, label, cover);
        queries <- rcons queries
          {| lq_kind = LiveHistoryCapabilityQuery member segment;
             lq_operation = Some node |};
        result <- Some output;
      }
    }

    return result;
  }
}.
