require import AllCore List FSet.
require import BeeKemTypes.

(* The log records every oracle attempt.  [bq_accepted] records the actual
   oracle result; it is never chosen by the adversary.  The causal frontiers
   are snapshots maintained by the challenger and are sufficient to derive the
   paper's q2op relation without a free safety parameter. *)
type beekem_query_kind = [
  | BeeQueryCreate
  | BeeQueryAdd
  | BeeQueryRemove
  | BeeQuerySendUpdate
  | BeeQueryDeliver
  | BeeQueryReveal
  | BeeQueryChallenge
  | BeeQueryCompromise
].

type beekem_query_rejection = [
  | BeeRejectAlreadyCreated
  | BeeRejectCreatorInInitialSet
  | BeeRejectInvalidMember
  | BeeRejectSelfModification
  | BeeRejectMissingSecret
  | BeeRejectAlreadyChallengedOrRevealed
  | BeeRejectAlreadyInHistory
  | BeeRejectShouldNotReceive
  | BeeRejectCausallyUnready
  | BeeRejectMissingControlMessage
  | BeeRejectProtocolFailure
].

type beekem_query = {
  bq_id : beekem_query_id;
  bq_kind : beekem_query_kind;
  bq_actor : beekem_user;
  bq_target : beekem_user option;
  bq_counter : beekem_counter option;
  bq_operation : beekem_operation_id option;
  bq_actor_frontier : beekem_operation_id fset;
  bq_target_frontier : beekem_operation_id fset;
  bq_accepted : bool;
  bq_rejection : beekem_query_rejection option
}.

type beekem_query_log = beekem_query list.

op beekem_query_is_create (q : beekem_query) : bool =
  q.`bq_kind = BeeQueryCreate.

op beekem_query_is_add (q : beekem_query) : bool =
  q.`bq_kind = BeeQueryAdd.

op beekem_query_is_remove (q : beekem_query) : bool =
  q.`bq_kind = BeeQueryRemove.

op beekem_query_is_send_update (q : beekem_query) : bool =
  q.`bq_kind = BeeQuerySendUpdate.

op beekem_query_is_deliver (q : beekem_query) : bool =
  q.`bq_kind = BeeQueryDeliver.

op beekem_query_is_reveal (q : beekem_query) : bool =
  q.`bq_kind = BeeQueryReveal.

op beekem_query_is_challenge (q : beekem_query) : bool =
  q.`bq_kind = BeeQueryChallenge.

op beekem_query_is_compromise (q : beekem_query) : bool =
  q.`bq_kind = BeeQueryCompromise.

op beekem_query_has_operation (q : beekem_query) : bool =
  q.`bq_operation <> None.

op beekem_query_successful (q : beekem_query) : bool =
  q.`bq_accepted /\ q.`bq_rejection = None.
