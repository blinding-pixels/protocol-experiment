require import AllCore List FSet.
require import ProtocolTypes ProtocolPrimitives UnauthorizedSignatureReduction.
require import UnauthorizedOriginGame LiveKeyGame.
require LiveBeeKemKiInterface.
clone import LiveBeeKemKiInterface as BKI.

import PG.

(* Transparent control-plane adapter to the KI-DCGKA oracle.  Application key
   outputs are simulated by the derived-output layer because the production
   live core otherwise reads its local BeeKEM secret store directly. *)
module BeeKemControlRuntime(O : BKI.BEEKEM_KI_ORACLE) = {
  proc init() : unit = { }

  proc create_group(
    creator : principal,
    initial_members : principal fset,
    digest : authorization_digest
  ) : beekem_step_result = {
    var result : beekem_step_result;
    result <@ O.create_group(creator, initial_members, digest);
    return result;
  }

  proc add_member(
    author : principal,
    target : principal,
    digest : authorization_digest
  ) : beekem_step_result = {
    var result : beekem_step_result;
    result <@ O.add_member(author, target, digest);
    return result;
  }

  proc remove_member(
    author : principal,
    target : principal,
    digest : authorization_digest
  ) : beekem_step_result = {
    var result : beekem_step_result;
    result <@ O.remove_member(author, target, digest);
    return result;
  }

  proc send_update(
    author : principal,
    digest : authorization_digest
  ) : beekem_step_result = {
    var result : beekem_step_result;
    result <@ O.send_update(author, digest);
    return result;
  }

  proc deliver(
    message : beekem_control_message,
    recipient : principal
  ) : beekem_secret option = {
    var result : beekem_secret option;
    result <@ O.deliver(message, recipient);
    return result;
  }

  proc compromise(member : principal) : beekem_snapshot = {
    var result : beekem_snapshot;
    result <@ O.compromise(member);
    return result;
  }
}.

type beekem_root_cache = principal -> node_id -> beekem_secret option.

op empty_beekem_root_cache : beekem_root_cache = fun _ _ => None.

op beekem_root_cache_put
    (cache : beekem_root_cache)
    (member : principal)
    (node : node_id)
    (secret : beekem_secret) : beekem_root_cache =
  fun candidate_member candidate_node =>
    if candidate_member = member /\ candidate_node = node
    then Some secret
    else cache candidate_member candidate_node.

(* One primitive Challenge call is made for the first derived output at a
   delivered (member,node) pair and its exact result is cached.  The application
   never receives the raw root.  The later L2 safety bridge must account for
   every pair inserted into this cache. *)
module KiBackedControl(
  Auth : ORIGIN_TRACKED_UNAUTHORIZED_ORACLE,
  O : BKI.BEEKEM_KI_ORACLE,
  K : MULTI_DOMAIN_KEY_SCHEDULE,
  R : LIVE_KEY_SAMPLER
) = {
  module B = BeeKemControlRuntime(O)
  module Core = LiveProtocolCore(Auth, B, K, R)

  var roots : beekem_root_cache
  var runtime_fault : bool

  proc init(
    initial_state : protocol_state,
    retention_kappa : int,
    challenge_bit : bool,
    initial_digest : authorization_digest
  ) : unit = {
    Core.init(initial_state, retention_kappa, challenge_bit, initial_digest);
    roots <- empty_beekem_root_cache;
    runtime_fault <- false;
  }

  proc root_for(
    member : principal,
    node : node_id
  ) : beekem_secret option = {
    var result : beekem_secret option;

    result <- roots member node;
    if (result = None) {
      result <@ O.challenge(member, node);
      if (result <> None) {
        roots <- beekem_root_cache_put roots member node (oget result);
      } else {
        runtime_fault <- true;
      }
    }

    return result;
  }
}.
