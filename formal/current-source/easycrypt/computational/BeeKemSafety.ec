require import AllCore List FSet.
require import BeeKemTypes BeeKemQueryLog.

(* Figure 3 writes q2op(q) as a single operation.  A compromised BeeKEM
   replica can have several maximal operations after a concurrent batch, so the
   executable model records the exact causal frontier at every query.  For an
   operation-bearing query q2op is the singleton containing that operation; for
   a successful snapshot compromise it is the challenger-recorded frontier.
   Relations below use the conservative frontier lifting: a left frontier must
   be causally covered by the right frontier, and concurrency is pairwise. *)
op beekem_operation_id_known
    (operations : beekem_operation list)
    (id : beekem_operation_id) : bool =
  with operations = [] => false
  with operations = operation :: rest =>
    operation.`bo_id = id \/ beekem_operation_id_known rest id.

op beekem_operation_id_precedes
    (operations : beekem_operation list)
    (earlier later : beekem_operation_id) : bool =
  with operations = [] => false
  with operations = operation :: rest =>
    (operation.`bo_id = later /\ earlier \in operation.`bo_ancestry) \/
    beekem_operation_id_precedes rest earlier later.

op beekem_operation_id_precedes_or_equals
    (operations : beekem_operation list)
    (earlier later : beekem_operation_id) : bool =
  earlier = later /\
    beekem_operation_id_known operations earlier \/
  beekem_operation_id_precedes operations earlier later.

op beekem_operation_ids_concurrent
    (operations : beekem_operation list)
    (left right : beekem_operation_id) : bool =
     left <> right
  /\ beekem_operation_id_known operations left
  /\ beekem_operation_id_known operations right
  /\ ! beekem_operation_id_precedes operations left right
  /\ ! beekem_operation_id_precedes operations right left.

op beekem_q2op_set (query : beekem_query) : beekem_operation_id fset =
  if ! beekem_query_successful query then fset0
  else if query.`bq_operation <> None
       then fset1 (oget query.`bq_operation)
       else if beekem_query_is_compromise query
            then query.`bq_actor_frontier
            else fset0.

op beekem_id_precedes_some
    (operations : beekem_operation list)
    (earlier : beekem_operation_id)
    (later_ids : beekem_operation_id list) : bool =
  with later_ids = [] => false
  with later_ids = later :: rest =>
    beekem_operation_id_precedes operations earlier later \/
    beekem_id_precedes_some operations earlier rest.

op beekem_id_precedes_or_equals_some
    (operations : beekem_operation list)
    (earlier : beekem_operation_id)
    (later_ids : beekem_operation_id list) : bool =
  with later_ids = [] => false
  with later_ids = later :: rest =>
    beekem_operation_id_precedes_or_equals operations earlier later \/
    beekem_id_precedes_or_equals_some operations earlier rest.

op beekem_ids_precede_frontier
    (operations : beekem_operation list)
    (earlier_ids later_ids : beekem_operation_id list) : bool =
  with earlier_ids = [] => true
  with earlier_ids = earlier :: rest =>
    beekem_id_precedes_some operations earlier later_ids /\
    beekem_ids_precede_frontier operations rest later_ids.

op beekem_ids_precede_or_equal_frontier
    (operations : beekem_operation list)
    (earlier_ids later_ids : beekem_operation_id list) : bool =
  with earlier_ids = [] => true
  with earlier_ids = earlier :: rest =>
    beekem_id_precedes_or_equals_some operations earlier later_ids /\
    beekem_ids_precede_or_equal_frontier operations rest later_ids.

op beekem_id_concurrent_with_all
    (operations : beekem_operation list)
    (left : beekem_operation_id)
    (right_ids : beekem_operation_id list) : bool =
  with right_ids = [] => true
  with right_ids = right :: rest =>
    beekem_operation_ids_concurrent operations left right /\
    beekem_id_concurrent_with_all operations left rest.

op beekem_ids_pairwise_concurrent
    (operations : beekem_operation list)
    (left_ids right_ids : beekem_operation_id list) : bool =
  with left_ids = [] => true
  with left_ids = left :: rest =>
    beekem_id_concurrent_with_all operations left right_ids /\
    beekem_ids_pairwise_concurrent operations rest right_ids.

op beekem_q2op_precedes
    (operations : beekem_operation list)
    (left right : beekem_query) : bool =
  let left_ids = elems (beekem_q2op_set left) in
  let right_ids = elems (beekem_q2op_set right) in
     left_ids <> []
  /\ right_ids <> []
  /\ beekem_ids_precede_frontier operations left_ids right_ids.

op beekem_q2op_precedes_or_equals
    (operations : beekem_operation list)
    (left right : beekem_query) : bool =
  let left_ids = elems (beekem_q2op_set left) in
  let right_ids = elems (beekem_q2op_set right) in
     left_ids <> []
  /\ right_ids <> []
  /\ beekem_ids_precede_or_equal_frontier operations left_ids right_ids.

op beekem_q2op_concurrent
    (operations : beekem_operation list)
    (left right : beekem_query) : bool =
  let left_ids = elems (beekem_q2op_set left) in
  let right_ids = elems (beekem_q2op_set right) in
     left_ids <> []
  /\ right_ids <> []
  /\ beekem_ids_pairwise_concurrent operations left_ids right_ids.

op beekem_successful_update_for
    (query : beekem_query)
    (id : beekem_user) : bool =
     beekem_query_successful query
  /\ beekem_query_is_send_update query
  /\ query.`bq_actor = id
  /\ query.`bq_operation <> None.

(* Search a finite query suffix for [remaining] causally ordered successful
   updates of [id], strictly after [lower] and ending no later than [upper].
   The recursion is structural on [candidates], so this is an executable finite
   predicate, not an existential assumption about a witness sequence. *)
op beekem_update_chain_between
    (operations : beekem_operation list)
    (candidates : beekem_query list)
    (id : beekem_user)
    (remaining : int)
    (lower upper : beekem_query) : bool =
  with candidates = [] =>
    if remaining <= 0
    then beekem_q2op_precedes_or_equals operations lower upper
    else false
  with candidates = candidate :: rest =>
    if remaining <= 0
    then beekem_q2op_precedes_or_equals operations lower upper
    else
      beekem_update_chain_between
        operations rest id remaining lower upper \/
      (beekem_successful_update_for candidate id /\
       beekem_q2op_precedes operations lower candidate /\
       beekem_update_chain_between
         operations rest id (remaining - 1) candidate upper).

(* Search for an ordered update chain that ends in the compromised snapshot.
   Unlike FSU there is no lower-bound relation to the challenged operation;
   CFS instead requires that challenge and compromise are on concurrent forks. *)
op beekem_update_chain_ending_at
    (operations : beekem_operation list)
    (candidates : beekem_query list)
    (id : beekem_user)
    (remaining : int)
    (upper : beekem_query) : bool =
  with candidates = [] =>
    remaining <= 0
  with candidates = candidate :: rest =>
    if remaining <= 0
    then true
    else
      beekem_update_chain_ending_at
        operations rest id remaining upper \/
      (beekem_successful_update_for candidate id /\
       beekem_q2op_precedes_or_equals operations candidate upper /\
       beekem_update_chain_between
         operations rest id (remaining - 1) candidate upper).

op beekem_kappa_fsu_clause
    (kappa : int)
    (operations : beekem_operation list)
    (queries : beekem_query_log)
    (challenge compromise : beekem_query) : bool =
  1 <= kappa /\
  beekem_update_chain_between
    operations queries compromise.`bq_actor kappa challenge compromise.

op beekem_pcs_clause
    (operations : beekem_operation list)
    (queries : beekem_query_log)
    (challenge compromise : beekem_query) : bool =
  beekem_update_chain_between
    operations queries compromise.`bq_actor 1 compromise challenge.

op beekem_kappa_cfs_clause
    (kappa : int)
    (operations : beekem_operation list)
    (queries : beekem_query_log)
    (challenge compromise : beekem_query) : bool =
     1 <= kappa
  /\ beekem_update_chain_ending_at
       operations queries compromise.`bq_actor kappa compromise
  /\ beekem_q2op_concurrent operations challenge compromise.

op beekem_challenge_compromise_pair_safe
    (kappa : int)
    (operations : beekem_operation list)
    (queries : beekem_query_log)
    (challenge compromise : beekem_query) : bool =
     beekem_kappa_fsu_clause
       kappa operations queries challenge compromise
  \/ beekem_pcs_clause
       operations queries challenge compromise
  \/ beekem_kappa_cfs_clause
       kappa operations queries challenge compromise.

op beekem_challenge_safe_against
    (kappa : int)
    (operations : beekem_operation list)
    (queries : beekem_query_log)
    (challenge : beekem_query)
    (candidates : beekem_query list) : bool =
  with candidates = [] => true
  with candidates = compromise :: rest =>
    ((! beekem_query_successful compromise \/
      ! beekem_query_is_compromise compromise) \/
      beekem_challenge_compromise_pair_safe
        kappa operations queries challenge compromise) /\
    beekem_challenge_safe_against
      kappa operations queries challenge rest.

op beekem_all_challenges_safe
    (kappa : int)
    (operations : beekem_operation list)
    (queries : beekem_query_log)
    (candidates : beekem_query list) : bool =
  with candidates = [] => true
  with candidates = challenge :: rest =>
    ((! beekem_query_successful challenge \/
      ! beekem_query_is_challenge challenge) \/
      beekem_challenge_safe_against
        kappa operations queries challenge queries) /\
    beekem_all_challenges_safe
      kappa operations queries rest.

(* Exact finite-kappa Figure 3 predicate over the actual challenger log.  The
   [operations] argument is the control-operation DAG maintained by Figure 8;
   neither argument is supplied as an admissibility oracle. *)
op bee_safe_kappa
    (kappa : int)
    (operations : beekem_operation list)
    (queries : beekem_query_log) : bool =
  1 <= kappa /\
  beekem_all_challenges_safe kappa operations queries queries.
