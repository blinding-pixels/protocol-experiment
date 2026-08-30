require import AllCore List FSet.

(* BeeKEM's protocol/game carriers are intentionally concrete wrappers.  The
   cryptographic algorithms are module parameters, while protocol state,
   message flow, causal ancestry, retention, and query accounting remain
   explicit data maintained by the challenger. *)
type beekem_user = [ BeeKemUser of int ].
type beekem_group = [ BeeKemGroup of int ].
type beekem_operation_id = [ BeeKemOperationId of int ].
type beekem_query_id = [ BeeKemQueryId of int ].
type beekem_tree_node_id = [ BeeKemTreeNodeId of int ].
type beekem_generation = [ BeeKemGeneration of int ].
type beekem_counter = [ BeeKemCounter of int ].
type beekem_public_key = [ BeeKemPublicKey of int ].
type beekem_secret_key = [ BeeKemSecretKey of int ].
type beekem_subgroup_secret = [ BeeKemSubgroupSecret of int ].
(* Figure 8 samples the ideal challenge uniformly from the same-length key
   space as the real secret.  Represent group secrets as concrete bitstrings so
   that the challenger can perform that draw directly rather than delegating it
   to an unconstrained sampler module. *)
type beekem_group_secret = [ BeeKemGroupSecret of bool list ].
type beekem_symmetric_key = [ BeeKemSymmetricKey of int ].
type beekem_ciphertext = [ BeeKemCiphertext of int ].
type beekem_control_payload = [ BeeKemControlPayload of int ].
type beekem_direct_payload = [ BeeKemDirectPayload of int ].
type beekem_random_secret = [ BeeKemRandomSecret of int ].

type beekem_operation_kind = [
  | BeeCreate
  | BeeAdd
  | BeeRemove
  | BeeUpdate
  | BeeResponse
].

type beekem_tree_position = [
  | BeeRoot
  | BeeLeftChild of beekem_tree_node_id
  | BeeRightChild of beekem_tree_node_id
].

type beekem_node_version = {
  bnv_public_key : beekem_public_key;
  bnv_ciphertexts : (beekem_public_key * beekem_ciphertext) list;
  bnv_established_by : beekem_operation_id
}.

type beekem_tree_node = {
  btn_id : beekem_tree_node_id;
  btn_position : beekem_tree_position;
  btn_blank : bool;
  btn_versions : beekem_node_version list
}.

type beekem_tree = {
  bt_root : beekem_tree_node_id option;
  bt_nodes : beekem_tree_node list;
  bt_leaf_of : beekem_user -> beekem_tree_node_id option
}.

type beekem_personal_secret = {
  bps_owner : beekem_user;
  bps_generation : beekem_generation;
  bps_public_key : beekem_public_key;
  bps_secret_key : beekem_secret_key;
  bps_established_by : beekem_operation_id
}.

(* A control operation carries its direct causal predecessors and its complete
   ancestry.  The challenger maintains the latter from the former; it is not an
   adversary-supplied admissibility bit. *)
type beekem_operation = {
  bo_id : beekem_operation_id;
  bo_group : beekem_group;
  bo_author : beekem_user;
  bo_author_counter : beekem_counter;
  bo_kind : beekem_operation_kind;
  bo_target : beekem_user option;
  bo_direct_predecessors : beekem_operation_id fset;
  bo_ancestry : beekem_operation_id fset;
  bo_leaf_public_key : beekem_public_key option;
  bo_version_path : (beekem_tree_node_id * beekem_node_version) list;
  bo_control_payload : beekem_control_payload
}.

type beekem_direct_message = {
  bdm_operation : beekem_operation_id;
  bdm_sender : beekem_user;
  bdm_recipient : beekem_user;
  bdm_payload : beekem_direct_payload
}.

(* Figure 8 uses two distinct non-key values.  [BeeSecretUndefined] models
   epsilon: an uninitialized entry or failed algorithm output.
   [BeeSecretNoOutput] models bottom: a defined protocol result with no group
   secret (BeeKEM Create/Add/Remove and some conflict states), and the value
   returned by a rejected oracle call.  Collapsing these cases would make the
   Figure 8 consistency checks and challenge reachability incorrect. *)
type beekem_secret_output = [
  | BeeSecretNoOutput
  | BeeSecretUndefined
  | BeeSecretValue of beekem_group_secret
].

type beekem_generated_message = {
  bgm_operation : beekem_operation;
  bgm_direct_messages : beekem_direct_message list;
  bgm_sender_secret : beekem_secret_output;
  bgm_needs_response : bool
}.

type beekem_member_state = {
  bms_user : beekem_user;
  bms_group : beekem_group option;
  bms_operations : beekem_operation list;
  bms_frontier : beekem_operation_id fset;
  bms_tree : beekem_tree;
  bms_leaf : beekem_tree_node_id option;
  bms_current_personal_secret : beekem_personal_secret;
  bms_retained_personal_secrets : beekem_personal_secret list;
  bms_current_group_secret : beekem_group_secret option;
  bms_pending_structural_operations : bool
}.

type beekem_protocol_result = {
  bpr_state : beekem_member_state;
  bpr_control : beekem_generated_message option;
  bpr_secret : beekem_secret_output
}.

type beekem_process_result = {
  bxr_state : beekem_member_state;
  bxr_control : beekem_generated_message option;
  bxr_sender_secret : beekem_secret_output;
  bxr_response_secret : beekem_secret_output
}.

type beekem_delivery = {
  bd_operation : beekem_operation_id;
  bd_sender : beekem_user;
  bd_recipient : beekem_user;
  bd_recipient_frontier_before : beekem_operation_id fset;
  bd_recipient_frontier_after : beekem_operation_id fset;
  bd_recipient_secret : beekem_secret_output;
  bd_response_operation : beekem_operation_id option
}.

type beekem_message_key = beekem_user * beekem_counter.
type beekem_direct_message_key = beekem_user * beekem_counter * beekem_user.

type beekem_member_state_map = beekem_user -> beekem_member_state option.
type beekem_counter_map = beekem_user -> int.
type beekem_message_map = beekem_message_key -> beekem_generated_message option.
type beekem_direct_message_map =
  beekem_direct_message_key -> beekem_direct_message option.
type beekem_secret_map = beekem_message_key -> beekem_secret_output.
type beekem_add_target_map = beekem_message_key -> beekem_user option.
type beekem_challenge_mark_map = beekem_message_key -> bool.
type beekem_needs_response_map = beekem_message_key -> bool.
type beekem_delivery_mark_map =
  beekem_user * beekem_counter * beekem_user -> bool.

type beekem_protocol_state = {
  bps_group : beekem_group option;
  bps_kappa : int;
  bps_initialized_users : beekem_user fset;
  bps_members : beekem_user fset;
  bps_member_states : beekem_member_state_map;
  bps_counters : beekem_counter_map;
  bps_messages : beekem_message_map;
  bps_direct_messages : beekem_direct_message_map;
  bps_secrets : beekem_secret_map;
  bps_add_targets : beekem_add_target_map;
  bps_challenge_marks : beekem_challenge_mark_map;
  bps_needs_responses : beekem_needs_response_map;
  bps_delivery_marks : beekem_delivery_mark_map;
  bps_operations : beekem_operation list;
  bps_deliveries : beekem_delivery list;
  bps_challenge_count : int;
  bps_member_addition_count : int
}.

op beekem_operation_precedes
  (earlier later : beekem_operation) : bool =
  earlier.`bo_id \in later.`bo_ancestry.

op beekem_operation_precedes_or_equals
  (earlier later : beekem_operation) : bool =
  earlier.`bo_id = later.`bo_id \/
  beekem_operation_precedes earlier later.

op beekem_operations_concurrent
  (left right : beekem_operation) : bool =
  left.`bo_id <> right.`bo_id /\
  ! beekem_operation_precedes left right /\
  ! beekem_operation_precedes right left.

op beekem_group_secret_bits
  (secret : beekem_group_secret) : bool list =
  with secret = BeeKemGroupSecret bits => bits.

op beekem_group_secret_length
  (secret : beekem_group_secret) : int =
  size (beekem_group_secret_bits secret).

op beekem_secret_output_is_no_output (output : beekem_secret_output) : bool =
  with output = BeeSecretNoOutput => true
  with output = BeeSecretUndefined => false
  with output = BeeSecretValue secret => false.

op beekem_secret_output_is_undefined (output : beekem_secret_output) : bool =
  with output = BeeSecretNoOutput => false
  with output = BeeSecretUndefined => true
  with output = BeeSecretValue secret => false.

op beekem_secret_output_is_value (output : beekem_secret_output) : bool =
  with output = BeeSecretNoOutput => false
  with output = BeeSecretUndefined => false
  with output = BeeSecretValue secret => true.

op beekem_secret_output_value
  (output : beekem_secret_output) : beekem_group_secret option =
  with output = BeeSecretNoOutput => None
  with output = BeeSecretUndefined => None
  with output = BeeSecretValue secret => Some secret.

(* [bms_current_personal_secret] is the newest personal secret; the list holds
   older retained secrets.  Thus finite-kappa retention bounds the current
   secret plus the retained suffix, matching "the kappa most recent personal
   secrets" rather than allowing kappa old secrets in addition to the current
   one. *)
op beekem_member_retention_valid
  (kappa : int)
  (member_state : beekem_member_state) : bool =
  1 <= kappa /\
  1 + size member_state.`bms_retained_personal_secrets <= kappa.

op beekem_operation_key
  (operation : beekem_operation) : beekem_message_key =
  (operation.`bo_author, operation.`bo_author_counter).

op beekem_member_state_map_set
  (states : beekem_member_state_map)
  (id : beekem_user)
  (value : beekem_member_state option) : beekem_member_state_map =
  fun candidate => if candidate = id then value else states candidate.

op beekem_counter_map_set
  (counters : beekem_counter_map)
  (id : beekem_user)
  (value : int) : beekem_counter_map =
  fun candidate => if candidate = id then value else counters candidate.

op beekem_message_map_set
  (messages : beekem_message_map)
  (key : beekem_message_key)
  (value : beekem_generated_message option) : beekem_message_map =
  fun candidate => if candidate = key then value else messages candidate.

op beekem_direct_message_map_set
  (messages : beekem_direct_message_map)
  (key : beekem_direct_message_key)
  (value : beekem_direct_message option) : beekem_direct_message_map =
  fun candidate => if candidate = key then value else messages candidate.

op beekem_secret_map_set
  (secrets : beekem_secret_map)
  (key : beekem_message_key)
  (value : beekem_secret_output) : beekem_secret_map =
  fun candidate => if candidate = key then value else secrets candidate.

op beekem_add_target_map_set
  (targets : beekem_add_target_map)
  (key : beekem_message_key)
  (value : beekem_user option) : beekem_add_target_map =
  fun candidate => if candidate = key then value else targets candidate.

op beekem_challenge_mark_map_set
  (marks : beekem_challenge_mark_map)
  (key : beekem_message_key)
  (value : bool) : beekem_challenge_mark_map =
  fun candidate => if candidate = key then value else marks candidate.

op beekem_needs_response_map_set
  (marks : beekem_needs_response_map)
  (key : beekem_message_key)
  (value : bool) : beekem_needs_response_map =
  fun candidate => if candidate = key then value else marks candidate.

op beekem_delivery_mark_map_set
  (marks : beekem_delivery_mark_map)
  (key : beekem_user * beekem_counter * beekem_user)
  (value : bool) : beekem_delivery_mark_map =
  fun candidate => if candidate = key then value else marks candidate.

op beekem_empty_protocol_state
  (group : beekem_group)
  (kappa : int) : beekem_protocol_state =
  {| bps_group = Some group;
     bps_kappa = kappa;
     bps_initialized_users = fset0;
     bps_members = fset0;
     bps_member_states = fun id => None;
     bps_counters = fun id => 0;
     bps_messages = fun key => None;
     bps_direct_messages = fun key => None;
     bps_secrets = fun key => BeeSecretUndefined;
     bps_add_targets = fun key => None;
     bps_challenge_marks = fun key => false;
     bps_needs_responses = fun key => false;
     bps_delivery_marks = fun key => false;
     bps_operations = [];
     bps_deliveries = [];
     bps_challenge_count = 0;
     bps_member_addition_count : int
}.
