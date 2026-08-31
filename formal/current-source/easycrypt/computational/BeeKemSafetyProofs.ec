require import AllCore List FSet.
require import BeeKemTypes BeeKemQueryLog BeeKemSafety.

(* Concrete Figure 3 traces.  Each operation has an explicit identifier,
   direct predecessor set, and transitive ancestry.  Each query records its
   actual operation or challenger-maintained compromise frontier. *)
op beekem_trace_group : beekem_group = BeeKemGroup 41.
op beekem_trace_challenged_user : beekem_user = BeeKemUser 1.
op beekem_trace_compromised_user : beekem_user = BeeKemUser 2.

op beekem_trace_operation
    (id : beekem_operation_id)
    (author : beekem_user)
    (counter : int)
    (kind : beekem_operation_kind)
    (direct ancestry : beekem_operation_id fset) : beekem_operation =
  {| bo_id = id;
     bo_group = beekem_trace_group;
     bo_author = author;
     bo_author_counter = BeeKemCounter counter;
     bo_kind = kind;
     bo_target = None;
     bo_direct_predecessors = direct;
     bo_ancestry = ancestry;
     bo_leaf_public_key = None;
     bo_version_path = [];
     bo_control_payload = BeeKemControlPayload counter |}.

op beekem_trace_query
    (id : int)
    (kind : beekem_query_kind)
    (actor : beekem_user)
    (operation : beekem_operation_id option)
    (frontier : beekem_operation_id fset) : beekem_query =
  {| bq_id = BeeKemQueryId id;
     bq_kind = kind;
     bq_actor = actor;
     bq_target = None;
     bq_counter = None;
     bq_operation = operation;
     bq_actor_frontier = frontier;
     bq_target_frontier = fset0;
     bq_accepted = true;
     bq_rejection = None |}.

(* kappa-FSU control: challenge, then three ordered updates by the eventually
   compromised user, then compromise at the third update. *)
op fsu_challenge_id : beekem_operation_id = BeeKemOperationId 10.
op fsu_update1_id : beekem_operation_id = BeeKemOperationId 11.
op fsu_update2_id : beekem_operation_id = BeeKemOperationId 12.
op fsu_update3_id : beekem_operation_id = BeeKemOperationId 13.

op fsu_challenge_operation : beekem_operation =
  beekem_trace_operation fsu_challenge_id beekem_trace_challenged_user 1
    BeeUpdate fset0 fset0.
op fsu_update1_operation : beekem_operation =
  beekem_trace_operation fsu_update1_id beekem_trace_compromised_user 1
    BeeUpdate (fset1 fsu_challenge_id) (fset1 fsu_challenge_id).
op fsu_update2_operation : beekem_operation =
  beekem_trace_operation fsu_update2_id beekem_trace_compromised_user 2
    BeeUpdate (fset1 fsu_update1_id)
      (fset1 fsu_challenge_id `|` fset1 fsu_update1_id).
op fsu_update3_operation : beekem_operation =
  beekem_trace_operation fsu_update3_id beekem_trace_compromised_user 3
    BeeUpdate (fset1 fsu_update2_id)
      (fset1 fsu_challenge_id `|` fset1 fsu_update1_id `|`
       fset1 fsu_update2_id).

op fsu_operations : beekem_operation list =
  [fsu_challenge_operation; fsu_update1_operation;
   fsu_update2_operation; fsu_update3_operation].

op fsu_challenge_query : beekem_query =
  beekem_trace_query 1 BeeQueryChallenge beekem_trace_challenged_user
    (Some fsu_challenge_id) (fset1 fsu_challenge_id).
op fsu_update1_query : beekem_query =
  beekem_trace_query 2 BeeQuerySendUpdate beekem_trace_compromised_user
    (Some fsu_update1_id) (fset1 fsu_update1_id).
op fsu_update2_query : beekem_query =
  beekem_trace_query 3 BeeQuerySendUpdate beekem_trace_compromised_user
    (Some fsu_update2_id) (fset1 fsu_update2_id).
op fsu_update3_query : beekem_query =
  beekem_trace_query 4 BeeQuerySendUpdate beekem_trace_compromised_user
    (Some fsu_update3_id) (fset1 fsu_update3_id).
op fsu_compromise_query : beekem_query =
  beekem_trace_query 5 BeeQueryCompromise beekem_trace_compromised_user
    None (fset1 fsu_update3_id).

op fsu_log : beekem_query_log =
  [fsu_challenge_query; fsu_update1_query; fsu_update2_query;
   fsu_update3_query; fsu_compromise_query].

op fsu_short_log : beekem_query_log =
  [fsu_challenge_query; fsu_update1_query;
   beekem_trace_query 3 BeeQueryCompromise beekem_trace_compromised_user
     None (fset1 fsu_update1_id)].

(* PCS control: compromise, one update by that user, then a challenge whose
   operation causally includes the update. *)
op pcs_compromise_id : beekem_operation_id = BeeKemOperationId 20.
op pcs_update_id : beekem_operation_id = BeeKemOperationId 21.
op pcs_challenge_id : beekem_operation_id = BeeKemOperationId 22.

op pcs_compromise_operation : beekem_operation =
  beekem_trace_operation pcs_compromise_id beekem_trace_compromised_user 1
    BeeCreate fset0 fset0.
op pcs_update_operation : beekem_operation =
  beekem_trace_operation pcs_update_id beekem_trace_compromised_user 2
    BeeUpdate (fset1 pcs_compromise_id) (fset1 pcs_compromise_id).
op pcs_challenge_operation : beekem_operation =
  beekem_trace_operation pcs_challenge_id beekem_trace_challenged_user 1
    BeeUpdate (fset1 pcs_update_id)
      (fset1 pcs_compromise_id `|` fset1 pcs_update_id).

op pcs_operations : beekem_operation list =
  [pcs_compromise_operation; pcs_update_operation; pcs_challenge_operation].
op pcs_compromise_query : beekem_query =
  beekem_trace_query 1 BeeQueryCompromise beekem_trace_compromised_user
    None (fset1 pcs_compromise_id).
op pcs_update_query : beekem_query =
  beekem_trace_query 2 BeeQuerySendUpdate beekem_trace_compromised_user
    (Some pcs_update_id) (fset1 pcs_update_id).
op pcs_challenge_query : beekem_query =
  beekem_trace_query 3 BeeQueryChallenge beekem_trace_challenged_user
    (Some pcs_challenge_id) (fset1 pcs_challenge_id).
op pcs_log : beekem_query_log =
  [pcs_compromise_query; pcs_update_query; pcs_challenge_query].
op pcs_rejected_log : beekem_query_log =
  [pcs_compromise_query; pcs_challenge_query].

(* kappa-CFS control: challenge and compromised fork are concurrent; the
   compromised fork contains two ordered updates by the compromised user. *)
op cfs_base_id : beekem_operation_id = BeeKemOperationId 30.
op cfs_challenge_id : beekem_operation_id = BeeKemOperationId 31.
op cfs_update1_id : beekem_operation_id = BeeKemOperationId 32.
op cfs_update2_id : beekem_operation_id = BeeKemOperationId 33.
op cfs_plain_fork_id : beekem_operation_id = BeeKemOperationId 34.

op cfs_base_operation : beekem_operation =
  beekem_trace_operation cfs_base_id beekem_trace_challenged_user 1
    BeeCreate fset0 fset0.
op cfs_challenge_operation : beekem_operation =
  beekem_trace_operation cfs_challenge_id beekem_trace_challenged_user 2
    BeeUpdate (fset1 cfs_base_id) (fset1 cfs_base_id).
op cfs_update1_operation : beekem_operation =
  beekem_trace_operation cfs_update1_id beekem_trace_compromised_user 1
    BeeUpdate (fset1 cfs_base_id) (fset1 cfs_base_id).
op cfs_update2_operation : beekem_operation =
  beekem_trace_operation cfs_update2_id beekem_trace_compromised_user 2
    BeeUpdate (fset1 cfs_update1_id)
      (fset1 cfs_base_id `|` fset1 cfs_update1_id).
op cfs_plain_fork_operation : beekem_operation =
  beekem_trace_operation cfs_plain_fork_id beekem_trace_compromised_user 3
    BeeResponse (fset1 cfs_base_id) (fset1 cfs_base_id).

op cfs_operations : beekem_operation list =
  [cfs_base_operation; cfs_challenge_operation;
   cfs_update1_operation; cfs_update2_operation; cfs_plain_fork_operation].
op cfs_challenge_query : beekem_query =
  beekem_trace_query 1 BeeQueryChallenge beekem_trace_challenged_user
    (Some cfs_challenge_id) (fset1 cfs_challenge_id).
op cfs_update1_query : beekem_query =
  beekem_trace_query 2 BeeQuerySendUpdate beekem_trace_compromised_user
    (Some cfs_update1_id) (fset1 cfs_update1_id).
op cfs_update2_query : beekem_query =
  beekem_trace_query 3 BeeQuerySendUpdate beekem_trace_compromised_user
    (Some cfs_update2_id) (fset1 cfs_update2_id).
op cfs_compromise_query : beekem_query =
  beekem_trace_query 4 BeeQueryCompromise beekem_trace_compromised_user
    None (fset1 cfs_update2_id).
op cfs_plain_compromise_query : beekem_query =
  beekem_trace_query 2 BeeQueryCompromise beekem_trace_compromised_user
    None (fset1 cfs_plain_fork_id).
op cfs_log : beekem_query_log =
  [cfs_challenge_query; cfs_update1_query;
   cfs_update2_query; cfs_compromise_query].
op cfs_rejected_log : beekem_query_log =
  [cfs_challenge_query; cfs_plain_compromise_query].

lemma fsu_trace_admissible_at_kappa_three :
  bee_safe_kappa 3 fsu_operations fsu_log.
proof.
  rewrite /bee_safe_kappa /fsu_log /beekem_all_challenges_safe
    /beekem_challenge_safe_against
    /beekem_challenge_compromise_pair_safe /beekem_kappa_fsu_clause
    /beekem_pcs_clause /beekem_kappa_cfs_clause
    /beekem_update_chain_between /beekem_update_chain_ending_at
    /beekem_successful_update_for /beekem_q2op_precedes
    /beekem_q2op_precedes_or_equals /beekem_q2op_concurrent
    /beekem_q2op_set /beekem_query_successful
    /beekem_query_is_send_update /beekem_query_is_challenge
    /beekem_query_is_compromise
    /fsu_challenge_query /fsu_update1_query /fsu_update2_query
    /fsu_update3_query /fsu_compromise_query /beekem_trace_query.
  rewrite (elems_fset1 fsu_challenge_id)
    (elems_fset1 fsu_update1_id)
    (elems_fset1 fsu_update2_id)
    (elems_fset1 fsu_update3_id).
  rewrite /beekem_ids_precede_frontier /beekem_ids_precede_or_equal_frontier
    /beekem_id_precedes_some /beekem_id_precedes_or_equals_some
    /beekem_operation_id_precedes /beekem_operation_id_precedes_or_equals
    /beekem_operation_id_known /fsu_operations
    /fsu_challenge_operation /fsu_update1_operation
    /fsu_update2_operation /fsu_update3_operation
    /beekem_trace_operation.
  smt(in_fset0 in_fset1 in_fsetU).
qed.

lemma fsu_kappa_one_boundary_admitted :
  bee_safe_kappa 1 fsu_operations fsu_short_log.
proof.
  rewrite /bee_safe_kappa /fsu_short_log /beekem_all_challenges_safe
    /beekem_challenge_safe_against
    /beekem_challenge_compromise_pair_safe /beekem_kappa_fsu_clause
    /beekem_pcs_clause /beekem_kappa_cfs_clause
    /beekem_update_chain_between /beekem_update_chain_ending_at
    /beekem_successful_update_for /beekem_q2op_precedes
    /beekem_q2op_precedes_or_equals /beekem_q2op_concurrent
    /beekem_q2op_set /beekem_query_successful
    /beekem_query_is_send_update /beekem_query_is_challenge
    /beekem_query_is_compromise
    /fsu_challenge_query /fsu_update1_query /beekem_trace_query.
  rewrite (elems_fset1 fsu_challenge_id)
    (elems_fset1 fsu_update1_id).
  rewrite /beekem_ids_precede_frontier /beekem_ids_precede_or_equal_frontier
    /beekem_id_precedes_some /beekem_id_precedes_or_equals_some
    /beekem_operation_id_precedes /beekem_operation_id_precedes_or_equals
    /beekem_operation_id_known /fsu_operations
    /fsu_challenge_operation /fsu_update1_operation
    /fsu_update2_operation /fsu_update3_operation
    /beekem_trace_operation.
  smt(in_fset0 in_fset1 in_fsetU).
qed.

lemma fsu_kappa_two_boundary_rejected :
  ! bee_safe_kappa 2 fsu_operations fsu_short_log.
proof.
  rewrite /bee_safe_kappa /fsu_short_log /beekem_all_challenges_safe
    /beekem_challenge_safe_against
    /beekem_challenge_compromise_pair_safe /beekem_kappa_fsu_clause
    /beekem_pcs_clause /beekem_kappa_cfs_clause
    /beekem_update_chain_between /beekem_update_chain_ending_at
    /beekem_successful_update_for /beekem_q2op_precedes
    /beekem_q2op_precedes_or_equals /beekem_q2op_concurrent
    /beekem_q2op_set /beekem_query_successful
    /beekem_query_is_send_update /beekem_query_is_challenge
    /beekem_query_is_compromise
    /fsu_challenge_query /fsu_update1_query /beekem_trace_query.
  rewrite (elems_fset1 fsu_challenge_id)
    (elems_fset1 fsu_update1_id).
  rewrite /beekem_ids_precede_frontier /beekem_ids_precede_or_equal_frontier
    /beekem_id_precedes_some /beekem_id_precedes_or_equals_some
    /beekem_ids_pairwise_concurrent /beekem_id_concurrent_with_all
    /beekem_operation_ids_concurrent
    /beekem_operation_id_precedes /beekem_operation_id_precedes_or_equals
    /beekem_operation_id_known /fsu_operations
    /fsu_challenge_operation /fsu_update1_operation
    /fsu_update2_operation /fsu_update3_operation
    /beekem_trace_operation.
  smt(in_fset0 in_fset1 in_fsetU).
qed.

lemma fsu_larger_finite_window_rejected_at_four :
  ! bee_safe_kappa 4 fsu_operations fsu_log.
proof.
  rewrite /bee_safe_kappa /fsu_log /beekem_all_challenges_safe
    /beekem_challenge_safe_against
    /beekem_challenge_compromise_pair_safe /beekem_kappa_fsu_clause
    /beekem_pcs_clause /beekem_kappa_cfs_clause
    /beekem_update_chain_between /beekem_update_chain_ending_at
    /beekem_successful_update_for /beekem_q2op_precedes
    /beekem_q2op_precedes_or_equals /beekem_q2op_concurrent
    /beekem_q2op_set /beekem_query_successful
    /beekem_query_is_send_update /beekem_query_is_challenge
    /beekem_query_is_compromise
    /fsu_challenge_query /fsu_update1_query /fsu_update2_query
    /fsu_update3_query /fsu_compromise_query /beekem_trace_query.
  rewrite (elems_fset1 fsu_challenge_id)
    (elems_fset1 fsu_update1_id)
    (elems_fset1 fsu_update2_id)
    (elems_fset1 fsu_update3_id).
  rewrite /beekem_ids_precede_frontier /beekem_ids_precede_or_equal_frontier
    /beekem_id_precedes_some /beekem_id_precedes_or_equals_some
    /beekem_ids_pairwise_concurrent /beekem_id_concurrent_with_all
    /beekem_operation_ids_concurrent
    /beekem_operation_id_precedes /beekem_operation_id_precedes_or_equals
    /beekem_operation_id_known /fsu_operations
    /fsu_challenge_operation /fsu_update1_operation
    /fsu_update2_operation /fsu_update3_operation
    /beekem_trace_operation.
  smt(in_fset0 in_fset1 in_fsetU).
qed.

lemma pcs_trace_admissible :
  bee_safe_kappa 1 pcs_operations pcs_log.
proof.
  rewrite /bee_safe_kappa /pcs_log /beekem_all_challenges_safe
    /beekem_challenge_safe_against
    /beekem_challenge_compromise_pair_safe /beekem_kappa_fsu_clause
    /beekem_pcs_clause /beekem_kappa_cfs_clause
    /beekem_update_chain_between /beekem_update_chain_ending_at
    /beekem_successful_update_for /beekem_q2op_precedes
    /beekem_q2op_precedes_or_equals /beekem_q2op_concurrent
    /beekem_q2op_set /beekem_query_successful
    /beekem_query_is_send_update /beekem_query_is_challenge
    /beekem_query_is_compromise
    /pcs_compromise_query /pcs_update_query /pcs_challenge_query
    /beekem_trace_query.
  rewrite (elems_fset1 pcs_compromise_id)
    (elems_fset1 pcs_update_id) (elems_fset1 pcs_challenge_id).
  rewrite /beekem_ids_precede_frontier /beekem_ids_precede_or_equal_frontier
    /beekem_id_precedes_some /beekem_id_precedes_or_equals_some
    /beekem_operation_id_precedes /beekem_operation_id_precedes_or_equals
    /beekem_operation_id_known /pcs_operations
    /pcs_compromise_operation /pcs_update_operation /pcs_challenge_operation
    /beekem_trace_operation.
  smt(in_fset0 in_fset1 in_fsetU).
qed.

lemma pcs_trace_without_healing_update_rejected :
  ! bee_safe_kappa 1 pcs_operations pcs_rejected_log.
proof.
  rewrite /bee_safe_kappa /pcs_rejected_log /beekem_all_challenges_safe
    /beekem_challenge_safe_against
    /beekem_challenge_compromise_pair_safe /beekem_kappa_fsu_clause
    /beekem_pcs_clause /beekem_kappa_cfs_clause
    /beekem_update_chain_between /beekem_update_chain_ending_at
    /beekem_successful_update_for /beekem_q2op_precedes
    /beekem_q2op_precedes_or_equals /beekem_q2op_concurrent
    /beekem_q2op_set /beekem_query_successful
    /beekem_query_is_send_update /beekem_query_is_challenge
    /beekem_query_is_compromise
    /pcs_compromise_query /pcs_challenge_query /beekem_trace_query.
  rewrite (elems_fset1 pcs_compromise_id)
    (elems_fset1 pcs_challenge_id).
  rewrite /beekem_ids_precede_frontier /beekem_ids_precede_or_equal_frontier
    /beekem_id_precedes_some /beekem_id_precedes_or_equals_some
    /beekem_ids_pairwise_concurrent /beekem_id_concurrent_with_all
    /beekem_operation_ids_concurrent
    /beekem_operation_id_precedes /beekem_operation_id_precedes_or_equals
    /beekem_operation_id_known /pcs_operations
    /pcs_compromise_operation /pcs_update_operation /pcs_challenge_operation
    /beekem_trace_operation.
  smt(in_fset0 in_fset1 in_fsetU).
qed.

lemma cfs_trace_admissible_at_kappa_two :
  bee_safe_kappa 2 cfs_operations cfs_log.
proof.
  rewrite /bee_safe_kappa /cfs_log /beekem_all_challenges_safe
    /beekem_challenge_safe_against
    /beekem_challenge_compromise_pair_safe /beekem_kappa_fsu_clause
    /beekem_pcs_clause /beekem_kappa_cfs_clause
    /beekem_update_chain_between /beekem_update_chain_ending_at
    /beekem_successful_update_for /beekem_q2op_precedes
    /beekem_q2op_precedes_or_equals /beekem_q2op_concurrent
    /beekem_q2op_set /beekem_query_successful
    /beekem_query_is_send_update /beekem_query_is_challenge
    /beekem_query_is_compromise
    /cfs_challenge_query /cfs_update1_query /cfs_update2_query
    /cfs_compromise_query /beekem_trace_query.
  rewrite (elems_fset1 cfs_challenge_id)
    (elems_fset1 cfs_update1_id) (elems_fset1 cfs_update2_id).
  rewrite /beekem_ids_precede_frontier /beekem_ids_precede_or_equal_frontier
    /beekem_id_precedes_some /beekem_id_precedes_or_equals_some
    /beekem_ids_pairwise_concurrent /beekem_id_concurrent_with_all
    /beekem_operation_ids_concurrent
    /beekem_operation_id_precedes /beekem_operation_id_precedes_or_equals
    /beekem_operation_id_known /cfs_operations
    /cfs_base_operation /cfs_challenge_operation
    /cfs_update1_operation /cfs_update2_operation /cfs_plain_fork_operation
    /beekem_trace_operation.
  smt(in_fset0 in_fset1 in_fsetU).
qed.

lemma cfs_trace_without_fork_updates_rejected :
  ! bee_safe_kappa 1 cfs_operations cfs_rejected_log.
proof.
  rewrite /bee_safe_kappa /cfs_rejected_log /beekem_all_challenges_safe
    /beekem_challenge_safe_against
    /beekem_challenge_compromise_pair_safe /beekem_kappa_fsu_clause
    /beekem_pcs_clause /beekem_kappa_cfs_clause
    /beekem_update_chain_between /beekem_update_chain_ending_at
    /beekem_successful_update_for /beekem_q2op_precedes
    /beekem_q2op_precedes_or_equals /beekem_q2op_concurrent
    /beekem_q2op_set /beekem_query_successful
    /beekem_query_is_send_update /beekem_query_is_challenge
    /beekem_query_is_compromise
    /cfs_challenge_query /cfs_plain_compromise_query /beekem_trace_query.
  rewrite (elems_fset1 cfs_challenge_id)
    (elems_fset1 cfs_plain_fork_id).
  rewrite /beekem_ids_precede_frontier /beekem_ids_precede_or_equal_frontier
    /beekem_id_precedes_some /beekem_id_precedes_or_equals_some
    /beekem_ids_pairwise_concurrent /beekem_id_concurrent_with_all
    /beekem_operation_ids_concurrent
    /beekem_operation_id_precedes /beekem_operation_id_precedes_or_equals
    /beekem_operation_id_known /cfs_operations
    /cfs_base_operation /cfs_challenge_operation
    /cfs_update1_operation /cfs_update2_operation /cfs_plain_fork_operation
    /beekem_trace_operation.
  smt(in_fset0 in_fset1 in_fsetU).
qed.

(* Structural clause characterizations: each concrete positive trace witnesses
   the intended disjunct itself, not merely the outer universal predicate. *)
lemma fsu_positive_uses_fsu_clause :
  beekem_kappa_fsu_clause 3 fsu_operations fsu_log
    fsu_challenge_query fsu_compromise_query.
proof.
  rewrite /beekem_kappa_fsu_clause /fsu_log /beekem_update_chain_between
    /beekem_successful_update_for /beekem_q2op_precedes
    /beekem_q2op_precedes_or_equals /beekem_q2op_set
    /beekem_query_successful /beekem_query_is_send_update
    /fsu_challenge_query /fsu_update1_query /fsu_update2_query
    /fsu_update3_query /fsu_compromise_query /beekem_trace_query.
  rewrite (elems_fset1 fsu_challenge_id)
    (elems_fset1 fsu_update1_id)
    (elems_fset1 fsu_update2_id)
    (elems_fset1 fsu_update3_id).
  rewrite /beekem_ids_precede_frontier /beekem_ids_precede_or_equal_frontier
    /beekem_id_precedes_some /beekem_id_precedes_or_equals_some
    /beekem_operation_id_precedes /beekem_operation_id_precedes_or_equals
    /beekem_operation_id_known /fsu_operations
    /fsu_challenge_operation /fsu_update1_operation
    /fsu_update2_operation /fsu_update3_operation /beekem_trace_operation.
  smt(in_fset0 in_fset1 in_fsetU).
qed.

lemma pcs_positive_uses_pcs_clause :
  beekem_pcs_clause pcs_operations pcs_log
    pcs_challenge_query pcs_compromise_query.
proof.
  rewrite /beekem_pcs_clause /pcs_log /beekem_update_chain_between
    /beekem_successful_update_for /beekem_q2op_precedes
    /beekem_q2op_precedes_or_equals /beekem_q2op_set
    /beekem_query_successful /beekem_query_is_send_update
    /pcs_compromise_query /pcs_update_query /pcs_challenge_query
    /beekem_trace_query.
  rewrite (elems_fset1 pcs_compromise_id)
    (elems_fset1 pcs_update_id) (elems_fset1 pcs_challenge_id).
  rewrite /beekem_ids_precede_frontier /beekem_ids_precede_or_equal_frontier
    /beekem_id_precedes_some /beekem_id_precedes_or_equals_some
    /beekem_operation_id_precedes /beekem_operation_id_precedes_or_equals
    /beekem_operation_id_known /pcs_operations
    /pcs_compromise_operation /pcs_update_operation /pcs_challenge_operation
    /beekem_trace_operation.
  smt(in_fset0 in_fset1 in_fsetU).
qed.

lemma cfs_positive_uses_cfs_clause :
  beekem_kappa_cfs_clause 2 cfs_operations cfs_log
    cfs_challenge_query cfs_compromise_query.
proof.
  rewrite /beekem_kappa_cfs_clause /cfs_log
    /beekem_update_chain_ending_at /beekem_update_chain_between
    /beekem_successful_update_for /beekem_q2op_precedes
    /beekem_q2op_precedes_or_equals /beekem_q2op_concurrent
    /beekem_q2op_set /beekem_query_successful
    /beekem_query_is_send_update
    /cfs_challenge_query /cfs_update1_query /cfs_update2_query
    /cfs_compromise_query /beekem_trace_query.
  rewrite (elems_fset1 cfs_challenge_id)
    (elems_fset1 cfs_update1_id) (elems_fset1 cfs_update2_id).
  rewrite /beekem_ids_precede_frontier /beekem_ids_precede_or_equal_frontier
    /beekem_id_precedes_some /beekem_id_precedes_or_equals_some
    /beekem_ids_pairwise_concurrent /beekem_id_concurrent_with_all
    /beekem_operation_ids_concurrent
    /beekem_operation_id_precedes /beekem_operation_id_precedes_or_equals
    /beekem_operation_id_known /cfs_operations
    /cfs_base_operation /cfs_challenge_operation
    /cfs_update1_operation /cfs_update2_operation /cfs_plain_fork_operation
    /beekem_trace_operation.
  smt(in_fset0 in_fset1 in_fsetU).
qed.
