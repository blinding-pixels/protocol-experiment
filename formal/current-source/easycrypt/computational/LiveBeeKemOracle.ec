require import AllCore List FSet.
require import ProtocolTypes ProtocolPrimitives UnauthorizedSignatureReduction.
require import UnauthorizedOriginGame LiveKeyGame LiveBeeKemDerived.

import PG.

(* Complete application oracle presented to the live adversary.  The production
   control/authentication core is unchanged; this adapter records the exact
   application query log consumed by bee-safe-kappa and delegates all derived
   outputs to [KiBackedDerived]. *)
module KiBackedLiveOracle(
  Auth : ORIGIN_TRACKED_UNAUTHORIZED_ORACLE,
  O : BKI.BEEKEM_KI_ORACLE,
  K : MULTI_DOMAIN_KEY_SCHEDULE,
  R : LIVE_KEY_SAMPLER
) = {
  module D = KiBackedDerived(Auth, O, K, R)

  proc init(
    initial_state : protocol_state,
    retention_kappa : int,
    challenge_bit : bool,
    initial_digest : authorization_digest
  ) : unit = {
    D.init(initial_state, retention_kappa, challenge_bit, initial_digest);
  }

  proc sign_operation(
    envelope : operation_envelope
  ) : signed_operation = {
    var result : signed_operation;
    result <@ D.Base.Core.sign_operation(envelope);
    return result;
  }

  proc sign_authorization_fact(
    fact : authorization_fact
  ) : signed_authorization_fact = {
    var result : signed_authorization_fact;
    result <@ D.Base.Core.sign_authorization_fact(fact);
    return result;
  }

  proc create_group(
    creator : principal,
    initial_members : principal fset
  ) : node_id option = {
    var result : node_id option;
    result <@ D.Base.Core.create_group(creator, initial_members);
    if (result <> None) {
      D.record(
        {| lq_kind = LiveCreateQuery creator;
           lq_operation = result |}
      );
    }
    return result;
  }

  proc add_member(
    author : principal,
    target : principal
  ) : node_id option = {
    var result : node_id option;
    result <@ D.Base.Core.add_member(author, target);
    if (result <> None) {
      D.record(
        {| lq_kind = LiveAddQuery author target;
           lq_operation = result |}
      );
    }
    return result;
  }

  proc remove_member(
    author : principal,
    target : principal
  ) : node_id option = {
    var result : node_id option;
    result <@ D.Base.Core.remove_member(author, target);
    if (result <> None) {
      D.record(
        {| lq_kind = LiveRemoveQuery author target;
           lq_operation = result |}
      );
    }
    return result;
  }

  proc send_beekem_update(author : principal) : node_id option = {
    var result : node_id option;
    result <@ D.Base.Core.send_beekem_update(author);
    if (result <> None) {
      D.record(
        {| lq_kind = LiveUpdateQuery author;
           lq_operation = result |}
      );
    }
    return result;
  }

  proc deliver(node : node_id, recipient : principal) : bool = {
    var message : beekem_control_message option;
    var result : bool;

    message <- D.Base.Core.controls node;
    result <@ D.Base.Core.deliver(node, recipient);
    if (result /\ message <> None) {
      D.record(
        {| lq_kind =
             LiveDeliverQuery (oget message).`bcm_author recipient;
           lq_operation = Some node |}
      );
    }
    return result;
  }

  proc reveal_live_key(
    member : principal,
    node : node_id
  ) : live_application_key option = {
    var result : live_application_key option;
    result <@ D.reveal_live_key(member, node);
    return result;
  }

  proc challenge_live(
    member : principal,
    node : node_id
  ) : live_application_key option = {
    var result : live_application_key option;
    result <@ D.challenge_live(member, node);
    return result;
  }

  proc reveal_history_output(
    member : principal,
    node : node_id,
    segment : segment_id
  ) : history_domain_output option = {
    var result : history_domain_output option;
    result <@ D.reveal_history_output(member, node, segment);
    return result;
  }

  proc reveal_history_capability(
    member : principal,
    node : node_id,
    segment : segment_id,
    cover : segment_cover
  ) : history_capability_output option = {
    var result : history_capability_output option;
    result <@ D.reveal_history_capability(member, node, segment, cover);
    return result;
  }

  proc compromise_protocol_state(
    member : principal
  ) : beekem_snapshot option = {
    var head : node_id option;
    var result : beekem_snapshot option;

    head <- D.Base.Core.member_heads member;
    result <@ D.Base.Core.compromise_protocol_state(member);
    if (result <> None) {
      D.record(
        {| lq_kind = LiveCompromiseQuery member;
           lq_operation = head |}
      );
    }
    return result;
  }

  proc submit_operation(
    operation : signed_operation,
    view : public_view
  ) : bool = {
    var envelope : operation_envelope option;
    var identifier : operation_id option;
    var result : bool;

    envelope <- decode_operation operation.`so_raw;
    identifier <-
      if envelope = None then None
      else Some (oget envelope).`oe_operation_id;
    result <@ D.Base.Core.submit_operation(operation, view);
    D.record(
      {| lq_kind = LiveSubmitOperationQuery identifier result;
         lq_operation = None |}
    );
    return result;
  }
}.
