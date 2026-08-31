require import AllCore List FSet.
require import ProtocolTypes CanonicalEncoding BeeKemTypes.
require import LiveKeyGame LivePrfTypes LivePrfGame.
require import LivePrfApplicationReduction.
require import LiveBeeKemAuthoritativeLiveTypes.

(* Real challenge schedule used on the BeeKEM side of the hybrid.  The existing
   primitive PRF challenger evaluates both its real and random challenge
   branches before selecting one.  This schedule mirrors that exact call trace
   on application challenge calls, discarding only the unused sampled key.  It
   keeps live reveals and both history domains on the real schedule. *)
module RealChallengeKeySchedule(
  K : MULTI_DOMAIN_KEY_SCHEDULE,
  R : LIVE_KEY_SAMPLER
) : PRF_ORACLE_BACKED_KEY_SCHEDULE = {
  var challenge_mode : bool

  proc init() : unit = {
    challenge_mode <- false;
  }

  proc begin_challenge() : unit = {
    challenge_mode <- true;
  }

  proc end_challenge() : unit = {
    challenge_mode <- false;
  }

  proc derive_live(
    secret : beekem_secret,
    label : live_key_label
  ) : live_application_key = {
    var real_key : live_application_key;
    var unused_random_key : live_application_key;

    real_key <@ K.derive_live(secret, label);
    unused_random_key <- witness;
    if (challenge_mode) {
      unused_random_key <@ R.sample(label);
    }
    return real_key;
  }

  proc derive_history(
    secret : beekem_secret,
    label : history_key_label
  ) : history_domain_output = {
    var result : history_domain_output;
    result <@ K.derive_history(secret, label);
    return result;
  }

  proc derive_history_capability(
    secret : beekem_secret,
    label : history_key_label,
    cover : segment_cover
  ) : history_capability_output = {
    var result : history_capability_output;
    result <@ K.derive_history_capability(secret, label, cover);
    return result;
  }
}.

(* Full-state authoritative analogue of [PrfBackedLiveOracle].  It forwards
   every application procedure unchanged and opens the challenger-owned PRF
   switch only around [challenge_live].  In particular, compromise returns the
   complete authoritative member state and no old single-generation snapshot
   is introduced. *)
module AuthoritativePrfBackedLiveOracle(
  Core : AUTHORITATIVE_LIVE_PROTOCOL_ORACLE,
  K : PRF_ORACLE_BACKED_KEY_SCHEDULE
) : AUTHORITATIVE_LIVE_PROTOCOL_ORACLE = {
  proc sign_operation(
    envelope : operation_envelope
  ) : signed_operation = {
    var result : signed_operation;
    result <@ Core.sign_operation(envelope);
    return result;
  }

  proc sign_authorization_fact(
    fact : authorization_fact
  ) : signed_authorization_fact = {
    var result : signed_authorization_fact;
    result <@ Core.sign_authorization_fact(fact);
    return result;
  }

  proc create_group(
    creator : principal,
    initial_members : principal fset
  ) : node_id option = {
    var result : node_id option;
    result <@ Core.create_group(creator, initial_members);
    return result;
  }

  proc add_member(
    author : principal,
    target : principal
  ) : node_id option = {
    var result : node_id option;
    result <@ Core.add_member(author, target);
    return result;
  }

  proc remove_member(
    author : principal,
    target : principal
  ) : node_id option = {
    var result : node_id option;
    result <@ Core.remove_member(author, target);
    return result;
  }

  proc send_beekem_update(
    author : principal
  ) : node_id option = {
    var result : node_id option;
    result <@ Core.send_beekem_update(author);
    return result;
  }

  proc deliver(
    node : node_id,
    recipient : principal
  ) : bool = {
    var result : bool;
    result <@ Core.deliver(node, recipient);
    return result;
  }

  proc reveal_live_key(
    member : principal,
    node : node_id
  ) : live_application_key option = {
    var result : live_application_key option;
    result <@ Core.reveal_live_key(member, node);
    return result;
  }

  proc challenge_live(
    member : principal,
    node : node_id
  ) : live_application_key option = {
    var result : live_application_key option;

    K.begin_challenge();
    result <@ Core.challenge_live(member, node);
    K.end_challenge();
    return result;
  }

  proc reveal_history_output(
    member : principal,
    node : node_id,
    segment : segment_id
  ) : history_domain_output option = {
    var result : history_domain_output option;
    result <@ Core.reveal_history_output(member, node, segment);
    return result;
  }

  proc reveal_history_capability(
    member : principal,
    node : node_id,
    segment : segment_id,
    cover : segment_cover
  ) : history_capability_output option = {
    var result : history_capability_output option;
    result <@ Core.reveal_history_capability(member, node, segment, cover);
    return result;
  }

  proc compromise_protocol_state(
    member : principal
  ) : beekem_member_state option = {
    var result : beekem_member_state option;
    result <@ Core.compromise_protocol_state(member);
    return result;
  }

  proc submit_operation(
    operation : signed_operation,
    view : public_view
  ) : bool = {
    var result : bool;
    result <@ Core.submit_operation(operation, view);
    return result;
  }
}.
