require import AllCore List FSet.
require import ProtocolTypes CanonicalEncoding.
require import LiveKeyGame BeeKemTypes.
require import LiveBeeKemAuthoritativeTypes.
require import LiveBeeKemAuthoritativeRootBridge.

(* Application-derived outputs retain the exact authoritative KI challenge root
   in the existing multi-domain key-schedule carrier.  The cache is indexed by
   the complete application (member,node) address: history and live-domain
   outputs at one address therefore use one challenger-owned root, while
   distinct members or nodes cannot alias. *)
type authoritative_application_root_cache =
  principal -> node_id -> beekem_secret option.

type authoritative_application_mark_store =
  principal -> node_id -> bool.

op empty_authoritative_application_root_cache :
    authoritative_application_root_cache =
  fun _ _ => None.

op authoritative_application_root_cache_put
    (cache : authoritative_application_root_cache)
    (member : principal)
    (node : node_id)
    (root : beekem_secret) : authoritative_application_root_cache =
  fun candidate_member candidate_node =>
    if candidate_member = member /\ candidate_node = node
    then Some root
    else cache candidate_member candidate_node.

op empty_authoritative_application_mark_store :
    authoritative_application_mark_store =
  fun _ _ => false.

op authoritative_application_mark_store_put
    (store : authoritative_application_mark_store)
    (member : principal)
    (node : node_id)
    (value : bool) : authoritative_application_mark_store =
  fun candidate_member candidate_node =>
    if candidate_member = member /\ candidate_node = node
    then value
    else store candidate_member candidate_node.

op application_beekem_root_bridge_value
    (bridge : application_beekem_root_bridge_result) : beekem_secret option =
  with bridge = ApplicationRootNoOutput => None
  with bridge = ApplicationRootUndefined => None
  with bridge = ApplicationRootValue root => Some root.

op application_beekem_output_root
    (output : beekem_secret_output option) : beekem_secret option =
  if output = None then None else
    application_beekem_root_bridge_value
      (application_beekem_root_bridge (oget output)).

lemma application_beekem_output_root_value
    (secret : beekem_group_secret) :
  application_beekem_output_root (Some (BeeSecretValue secret)) =
  Some
    (application_beekem_root_of_authoritative
      (authoritative_application_root_of_beekem secret)).
proof. by done. qed.

lemma authoritative_application_root_cache_put_exact
    (cache : authoritative_application_root_cache)
    (member : principal)
    (node : node_id)
    (root : beekem_secret) :
  authoritative_application_root_cache_put
    cache member node root member node = Some root.
proof. by rewrite /authoritative_application_root_cache_put. qed.

(* This is the final application-facing oracle shape.  The compromise result is
   the complete authoritative member state, including its potentially
   multi-operation frontier; the old single-generation snapshot type does not
   occur in this interface. *)
module type AUTHORITATIVE_LIVE_PROTOCOL_ORACLE = {
  proc sign_operation(envelope : operation_envelope) : signed_operation
  proc sign_authorization_fact(
    fact : authorization_fact
  ) : signed_authorization_fact

  proc create_group(
    creator : principal,
    initial_members : principal fset
  ) : node_id option

  proc add_member(author : principal, target : principal) : node_id option
  proc remove_member(author : principal, target : principal) : node_id option
  proc send_beekem_update(author : principal) : node_id option
  proc deliver(node : node_id, recipient : principal) : bool

  proc reveal_live_key(
    member : principal,
    node : node_id
  ) : live_application_key option

  proc challenge_live(
    member : principal,
    node : node_id
  ) : live_application_key option

  proc reveal_history_output(
    member : principal,
    node : node_id,
    segment : segment_id
  ) : history_domain_output option

  proc reveal_history_capability(
    member : principal,
    node : node_id,
    segment : segment_id,
    cover : segment_cover
  ) : history_capability_output option

  proc compromise_protocol_state(
    member : principal
  ) : beekem_member_state option

  proc submit_operation(
    operation : signed_operation,
    view : public_view
  ) : bool
}.

module type AUTHORITATIVE_LIVE_KEY_ADVERSARY(
  O : AUTHORITATIVE_LIVE_PROTOCOL_ORACLE
) = {
  proc attack() : unit
  proc guess() : bool
}.
