require import AllCore List FSet.
require import ProtocolTypes BeeKemTypes BeeKemQueryLog.
require import LiveBeeKemAuthoritativeTypes.

(* Challenger-owned application metadata for translating application requests
   to the authoritative BeeKEM oracle.  None of these stores replace BeeKEM's
   protocol state or query log; they retain only the cross-layer correspondence
   that the later simulation proof must relate to those canonical objects. *)
type application_beekem_counter_store = principal -> int.
type application_beekem_digest_store =
  node_id -> authorization_digest option.
type application_beekem_delivery_store = principal -> node_id -> bool.

op empty_application_beekem_counter_store :
    application_beekem_counter_store =
  fun _ => 0.

op application_beekem_counter_store_put
    (store : application_beekem_counter_store)
    (member : principal)
    (value : int) : application_beekem_counter_store =
  fun candidate => if candidate = member then value else store candidate.

op empty_application_beekem_digest_store :
    application_beekem_digest_store =
  fun _ => None.

op application_beekem_digest_store_put
    (store : application_beekem_digest_store)
    (node : node_id)
    (digest : authorization_digest option) :
    application_beekem_digest_store =
  fun candidate => if candidate = node then digest else store candidate.

op empty_application_beekem_delivery_store :
    application_beekem_delivery_store =
  fun _ _ => false.

op application_beekem_delivery_store_put
    (store : application_beekem_delivery_store)
    (member : principal)
    (node : node_id)
    (value : bool) : application_beekem_delivery_store =
  fun candidate_member candidate_node =>
    if candidate_member = member /\ candidate_node = node
    then value
    else store candidate_member candidate_node.

lemma application_beekem_counter_store_put_exact
    (store : application_beekem_counter_store)
    (member : principal)
    (value : int) :
  application_beekem_counter_store_put store member value member = value.
proof. by rewrite /application_beekem_counter_store_put. qed.

lemma application_beekem_digest_store_put_exact
    (store : application_beekem_digest_store)
    (node : node_id)
    (digest : authorization_digest option) :
  application_beekem_digest_store_put store node digest node = digest.
proof. by rewrite /application_beekem_digest_store_put. qed.

lemma application_beekem_delivery_store_put_exact
    (store : application_beekem_delivery_store)
    (member : principal)
    (node : node_id)
    (value : bool) :
  application_beekem_delivery_store_put
    store member node value member node = value.
proof. by rewrite /application_beekem_delivery_store_put. qed.

(* Every member in an application set is translated through the explicit
   bidirectional registry.  A missing entry rejects the application request
   before any authoritative oracle call; no default BeeKEM identity is forged. *)
op application_beekem_users_of_list
    (registry : application_user_registry)
    (members : principal list) : beekem_user list option =
  with members = [] => Some []
  with members = member :: rest =>
    let user = registry.`aur_user_of member in
    let mapped_rest = application_beekem_users_of_list registry rest in
    if user = None \/ mapped_rest = None
    then None
    else Some (oget user :: oget mapped_rest).

op application_beekem_users_of_set
    (registry : application_user_registry)
    (members : principal fset) : beekem_user fset option =
  let mapped = application_beekem_users_of_list registry (elems members) in
  if mapped = None then None else Some (oflist (oget mapped)).

lemma application_beekem_users_of_empty_set
    (registry : application_user_registry) :
  application_beekem_users_of_set registry fset0 = Some fset0.
proof.
  rewrite /application_beekem_users_of_set /application_beekem_users_of_list.
  rewrite elems_fset0 /oflist.
  done.
qed.

type application_beekem_mapping_rejection = [
  | ApplicationBeeKemUnmappedActor
  | ApplicationBeeKemUnmappedTarget
  | ApplicationBeeKemUnmappedInitialMember
  | ApplicationBeeKemUnknownNode
  | ApplicationBeeKemUndeliveredNode
  | ApplicationBeeKemMissingControl
  | ApplicationBeeKemAddressCollision
  | ApplicationBeeKemControlMismatch
].

type application_beekem_attempt_kind = [
  | ApplicationBeeKemCreateAttempt of principal * principal fset
  | ApplicationBeeKemAddAttempt of principal * principal
  | ApplicationBeeKemRemoveAttempt of principal * principal
  | ApplicationBeeKemUpdateAttempt of principal
  | ApplicationBeeKemDeliverAttempt of node_id * principal
  | ApplicationBeeKemRevealAttempt of principal * node_id
  | ApplicationBeeKemChallengeAttempt of principal * node_id
  | ApplicationBeeKemCompromiseAttempt of principal
].

type application_beekem_attempt = {
  aba_kind : application_beekem_attempt_kind;
  aba_forwarded : bool;
  aba_canonical_query_id : beekem_query_id option;
  aba_canonical_accepted : bool;
  aba_node : node_id option;
  aba_address : application_beekem_address option;
  aba_control : beekem_generated_message option;
  aba_direct : beekem_direct_message option;
  aba_secret_output : beekem_secret_output option;
  aba_root_output : authoritative_application_root_result option;
  aba_compromise : beekem_member_state option;
  aba_compromise_frontier : beekem_operation_id fset;
  aba_mapping_rejection : application_beekem_mapping_rejection option
}.

type application_beekem_attempt_log = application_beekem_attempt list.

op application_beekem_next_query_id
    (forwarded_count : int) : beekem_query_id =
  BeeKemQueryId (forwarded_count + 1).

op application_beekem_output_mapping_exact
    (output : beekem_secret_output option)
    (root : authoritative_application_root_result option) : bool =
  if output = None
  then root = None
  else root = Some
    (authoritative_application_root_result_of_beekem (oget output)).

op application_beekem_attempt_output_exact
    (attempt : application_beekem_attempt) : bool =
  application_beekem_output_mapping_exact
    attempt.`aba_secret_output attempt.`aba_root_output.

lemma application_beekem_output_mapping_none :
  application_beekem_output_mapping_exact None None.
proof. by rewrite /application_beekem_output_mapping_exact. qed.

lemma application_beekem_output_mapping_some
    (output : beekem_secret_output) :
  application_beekem_output_mapping_exact
    (Some output)
    (Some (authoritative_application_root_result_of_beekem output)).
proof. by rewrite /application_beekem_output_mapping_exact. qed.

(* A forwarded adapter event names exactly one canonical query.  Rejected
   canonical calls still satisfy this predicate; acceptance is copied from the
   canonical query rather than inferred from an output shape. *)
op application_beekem_attempt_matches_query
    (attempt : application_beekem_attempt)
    (query : beekem_query) : bool =
  attempt.`aba_forwarded /\
  attempt.`aba_canonical_query_id = Some query.`bq_id /\
  attempt.`aba_canonical_accepted = query.`bq_accepted.

op application_beekem_attempt_is_local_rejection
    (attempt : application_beekem_attempt) : bool =
  ! attempt.`aba_forwarded /\
  attempt.`aba_canonical_query_id = None /\
  attempt.`aba_mapping_rejection <> None.

lemma application_beekem_forwarded_attempt_not_local_rejection
    (attempt : application_beekem_attempt)
    (query : beekem_query) :
  application_beekem_attempt_matches_query attempt query =>
  ! application_beekem_attempt_is_local_rejection attempt.
proof.
  rewrite /application_beekem_attempt_matches_query
    /application_beekem_attempt_is_local_rejection.
  smt().
qed.

type application_beekem_step_result = {
  abs_accepted : bool;
  abs_node : node_id option;
  abs_address : application_beekem_address option;
  abs_control : beekem_generated_message option;
  abs_secret_output : beekem_secret_output option;
  abs_root_output : authoritative_application_root_result option;
  abs_canonical_query_id : beekem_query_id option;
  abs_runtime_fault : bool
}.

type application_beekem_delivery_result = {
  abd_accepted : bool;
  abd_control : beekem_generated_message option;
  abd_direct : beekem_direct_message option;
  abd_response_node : node_id option;
  abd_canonical_query_id : beekem_query_id option;
  abd_runtime_fault : bool
}.

type application_beekem_output_result = {
  abo_forwarded : bool;
  abo_canonical_accepted : bool;
  abo_secret_output : beekem_secret_output option;
  abo_root_output : authoritative_application_root_result option;
  abo_address : application_beekem_address option;
  abo_canonical_query_id : beekem_query_id option;
  abo_runtime_fault : bool
}.

type application_beekem_compromise_result = {
  abc_forwarded : bool;
  abc_state : beekem_member_state option;
  abc_frontier : beekem_operation_id fset;
  abc_canonical_query_id : beekem_query_id option;
  abc_runtime_fault : bool
}.
