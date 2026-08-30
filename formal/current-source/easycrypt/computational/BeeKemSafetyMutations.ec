require import AllCore List FSet.
require import BeeKemTypes BeeKemQueryLog BeeKemSafety BeeKemSafetyProofs.

(* Each constructor below changes one condition of the executable Figure 3
   predicate.  The exact predicate remains [bee_safe_kappa]; these variants are
   negative controls only and are never imported by the theorem boundary. *)
type beekem_safety_mutation = [
  | BeeMutationDropFsuUpdateChain
  | BeeMutationDropPcsHealingUpdate
  | BeeMutationDropCfsUpdateChain
  | BeeMutationIgnoreCompromiseLog
  | BeeMutationIgnoreCausalAncestry
].

op beekem_q2op_frontiers_differ
    (left right : beekem_query) : bool =
  let left_set = beekem_q2op_set left in
  let right_set = beekem_q2op_set right in
     left_set <> fset0
  /\ right_set <> fset0
  /\ left_set <> right_set.

op beekem_mutated_fsu_clause
    (mutation : beekem_safety_mutation)
    (kappa : int)
    (operations : beekem_operation list)
    (queries : beekem_query_log)
    (challenge compromise : beekem_query) : bool =
  if mutation = BeeMutationDropFsuUpdateChain
  then 1 <= kappa /\
       beekem_q2op_precedes_or_equals operations challenge compromise
  else beekem_kappa_fsu_clause
         kappa operations queries challenge compromise.

op beekem_mutated_pcs_clause
    (mutation : beekem_safety_mutation)
    (operations : beekem_operation list)
    (queries : beekem_query_log)
    (challenge compromise : beekem_query) : bool =
  if mutation = BeeMutationDropPcsHealingUpdate
  then beekem_q2op_precedes_or_equals operations compromise challenge
  else beekem_pcs_clause operations queries challenge compromise.

op beekem_mutated_cfs_clause
    (mutation : beekem_safety_mutation)
    (kappa : int)
    (operations : beekem_operation list)
    (queries : beekem_query_log)
    (challenge compromise : beekem_query) : bool =
  if mutation = BeeMutationDropCfsUpdateChain
  then 1 <= kappa /\ beekem_q2op_concurrent operations challenge compromise
  else if mutation = BeeMutationIgnoreCausalAncestry
       then 1 <= kappa /\
            beekem_update_chain_ending_at
              operations queries compromise.`bq_actor kappa compromise /\
            beekem_q2op_frontiers_differ challenge compromise
       else beekem_kappa_cfs_clause
              kappa operations queries challenge compromise.

op beekem_mutated_pair_safe
    (mutation : beekem_safety_mutation)
    (kappa : int)
    (operations : beekem_operation list)
    (queries : beekem_query_log)
    (challenge compromise : beekem_query) : bool =
     beekem_mutated_fsu_clause
       mutation kappa operations queries challenge compromise
  \/ beekem_mutated_pcs_clause
       mutation operations queries challenge compromise
  \/ beekem_mutated_cfs_clause
       mutation kappa operations queries challenge compromise.

op beekem_mutated_challenge_safe_against
    (mutation : beekem_safety_mutation)
    (kappa : int)
    (operations : beekem_operation list)
    (queries : beekem_query_log)
    (challenge : beekem_query)
    (candidates : beekem_query list) : bool =
  with candidates = [] => true
  with candidates = compromise :: rest =>
    ((! beekem_query_successful compromise \/
      ! beekem_query_is_compromise compromise \/
      mutation = BeeMutationIgnoreCompromiseLog) \/
      beekem_mutated_pair_safe
        mutation kappa operations queries challenge compromise) /\
    beekem_mutated_challenge_safe_against
      mutation kappa operations queries challenge rest.

op beekem_mutated_all_challenges_safe
    (mutation : beekem_safety_mutation)
    (kappa : int)
    (operations : beekem_operation list)
    (queries : beekem_query_log)
    (candidates : beekem_query list) : bool =
  with candidates = [] => true
  with candidates = challenge :: rest =>
    ((! beekem_query_successful challenge \/
      ! beekem_query_is_challenge challenge) \/
      beekem_mutated_challenge_safe_against
        mutation kappa operations queries challenge queries) /\
    beekem_mutated_all_challenges_safe
      mutation kappa operations queries rest.

op bee_safe_kappa_mutated
    (mutation : beekem_safety_mutation)
    (kappa : int)
    (operations : beekem_operation list)
    (queries : beekem_query_log) : bool =
  1 <= kappa /\
  beekem_mutated_all_challenges_safe
    mutation kappa operations queries queries.

(* A causally related challenge/compromise pair with a valid update ending at
   the compromised frontier.  Exact CFS rejects it because it is not a fork. *)
op causal_mutation_update_id : beekem_operation_id = BeeKemOperationId 40.
op causal_mutation_challenge_id : beekem_operation_id = BeeKemOperationId 41.

op causal_mutation_update_operation : beekem_operation =
  beekem_trace_operation causal_mutation_update_id
    beekem_trace_compromised_user 1 BeeUpdate fset0 fset0.

op causal_mutation_challenge_operation : beekem_operation =
  beekem_trace_operation causal_mutation_challenge_id
    beekem_trace_challenged_user 1 BeeUpdate
    (fset1 causal_mutation_update_id) (fset1 causal_mutation_update_id).

op causal_mutation_operations : beekem_operation list =
  [causal_mutation_update_operation; causal_mutation_challenge_operation].

op causal_mutation_update_query : beekem_query =
  beekem_trace_query 1 BeeQuerySendUpdate beekem_trace_compromised_user
    (Some causal_mutation_update_id) (fset1 causal_mutation_update_id).

op causal_mutation_compromise_query : beekem_query =
  beekem_trace_query 2 BeeQueryCompromise beekem_trace_compromised_user
    None (fset1 causal_mutation_update_id).

op causal_mutation_challenge_query : beekem_query =
  beekem_trace_query 3 BeeQueryChallenge beekem_trace_challenged_user
    (Some causal_mutation_challenge_id)
    (fset1 causal_mutation_challenge_id).

op causal_mutation_log : beekem_query_log =
  [causal_mutation_update_query; causal_mutation_compromise_query;
   causal_mutation_challenge_query].

lemma mutation_drop_fsu_chain_admits_short_exposure :
  bee_safe_kappa_mutated BeeMutationDropFsuUpdateChain
    2 fsu_operations fsu_short_log.
proof.
  rewrite /bee_safe_kappa_mutated /beekem_mutated_all_challenges_safe
    /beekem_mutated_challenge_safe_against /beekem_mutated_pair_safe
    /beekem_mutated_fsu_clause /beekem_mutated_pcs_clause
    /beekem_mutated_cfs_clause /fsu_short_log
    /beekem_kappa_fsu_clause /beekem_pcs_clause /beekem_kappa_cfs_clause
    /beekem_update_chain_between /beekem_update_chain_ending_at
    /beekem_successful_update_for /beekem_q2op_precedes
    /beekem_q2op_precedes_or_equals /beekem_q2op_concurrent
    /beekem_q2op_set /beekem_query_successful
    /beekem_query_is_send_update /beekem_query_is_challenge
    /beekem_query_is_compromise
    /fsu_challenge_query /fsu_update1_query /beekem_trace_query.
  rewrite (elems_fset1 fsu_challenge_id) (elems_fset1 fsu_update1_id).
  rewrite /beekem_ids_precede_frontier /beekem_ids_precede_or_equal_frontier
    /beekem_id_precedes_some /beekem_id_precedes_or_equals_some
    /beekem_ids_pairwise_concurrent /beekem_id_concurrent_with_all
    /beekem_operation_ids_concurrent
    /beekem_operation_id_precedes /beekem_operation_id_precedes_or_equals
    /beekem_operation_id_known /fsu_operations
    /fsu_challenge_operation /fsu_update1_operation
    /fsu_update2_operation /fsu_update3_operation /beekem_trace_operation.
  smt(in_fset0 in_fset1 in_fsetU).
qed.

lemma mutation_drop_pcs_update_admits_unhealed_exposure :
  bee_safe_kappa_mutated BeeMutationDropPcsHealingUpdate
    1 pcs_operations pcs_rejected_log.
proof.
  rewrite /bee_safe_kappa_mutated /beekem_mutated_all_challenges_safe
    /beekem_mutated_challenge_safe_against /beekem_mutated_pair_safe
    /beekem_mutated_fsu_clause /beekem_mutated_pcs_clause
    /beekem_mutated_cfs_clause /pcs_rejected_log
    /beekem_kappa_fsu_clause /beekem_pcs_clause /beekem_kappa_cfs_clause
    /beekem_update_chain_between /beekem_update_chain_ending_at
    /beekem_successful_update_for /beekem_q2op_precedes
    /beekem_q2op_precedes_or_equals /beekem_q2op_concurrent
    /beekem_q2op_set /beekem_query_successful
    /beekem_query_is_send_update /beekem_query_is_challenge
    /beekem_query_is_compromise
    /pcs_compromise_query /pcs_challenge_query /beekem_trace_query.
  rewrite (elems_fset1 pcs_compromise_id) (elems_fset1 pcs_challenge_id).
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

lemma mutation_drop_cfs_chain_admits_unupdated_fork :
  bee_safe_kappa_mutated BeeMutationDropCfsUpdateChain
    1 cfs_operations cfs_rejected_log.
proof.
  rewrite /bee_safe_kappa_mutated /beekem_mutated_all_challenges_safe
    /beekem_mutated_challenge_safe_against /beekem_mutated_pair_safe
    /beekem_mutated_fsu_clause /beekem_mutated_pcs_clause
    /beekem_mutated_cfs_clause /cfs_rejected_log
    /beekem_kappa_fsu_clause /beekem_pcs_clause /beekem_kappa_cfs_clause
    /beekem_update_chain_between /beekem_update_chain_ending_at
    /beekem_successful_update_for /beekem_q2op_precedes
    /beekem_q2op_precedes_or_equals /beekem_q2op_concurrent
    /beekem_q2op_set /beekem_query_successful
    /beekem_query_is_send_update /beekem_query_is_challenge
    /beekem_query_is_compromise
    /cfs_challenge_query /cfs_plain_compromise_query /beekem_trace_query.
  rewrite (elems_fset1 cfs_challenge_id) (elems_fset1 cfs_plain_fork_id).
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

lemma mutation_ignore_compromise_log_admits_unsafe_trace :
  bee_safe_kappa_mutated BeeMutationIgnoreCompromiseLog
    1 pcs_operations pcs_rejected_log.
proof.
  rewrite /bee_safe_kappa_mutated /beekem_mutated_all_challenges_safe
    /beekem_mutated_challenge_safe_against /beekem_mutated_pair_safe
    /beekem_mutated_fsu_clause /beekem_mutated_pcs_clause
    /beekem_mutated_cfs_clause /pcs_rejected_log
    /beekem_query_successful /beekem_query_is_challenge
    /beekem_query_is_compromise /pcs_compromise_query
    /pcs_challenge_query /beekem_trace_query.
  trivial.
qed.

lemma exact_causal_trace_is_rejected :
  ! bee_safe_kappa 1 causal_mutation_operations causal_mutation_log.
proof.
  rewrite /bee_safe_kappa /causal_mutation_log /beekem_all_challenges_safe
    /beekem_challenge_safe_against /beekem_challenge_compromise_pair_safe
    /beekem_kappa_fsu_clause /beekem_pcs_clause /beekem_kappa_cfs_clause
    /beekem_update_chain_between /beekem_update_chain_ending_at
    /beekem_successful_update_for /beekem_q2op_precedes
    /beekem_q2op_precedes_or_equals /beekem_q2op_concurrent
    /beekem_q2op_set /beekem_query_successful
    /beekem_query_is_send_update /beekem_query_is_challenge
    /beekem_query_is_compromise
    /causal_mutation_update_query /causal_mutation_compromise_query
    /causal_mutation_challenge_query /beekem_trace_query.
  rewrite (elems_fset1 causal_mutation_update_id)
    (elems_fset1 causal_mutation_challenge_id).
  rewrite /beekem_ids_precede_frontier /beekem_ids_precede_or_equal_frontier
    /beekem_id_precedes_some /beekem_id_precedes_or_equals_some
    /beekem_ids_pairwise_concurrent /beekem_id_concurrent_with_all
    /beekem_operation_ids_concurrent
    /beekem_operation_id_precedes /beekem_operation_id_precedes_or_equals
    /beekem_operation_id_known /causal_mutation_operations
    /causal_mutation_update_operation /causal_mutation_challenge_operation
    /beekem_trace_operation.
  smt(in_fset0 in_fset1).
qed.

lemma mutation_ignore_ancestry_admits_causal_nonfork :
  bee_safe_kappa_mutated BeeMutationIgnoreCausalAncestry
    1 causal_mutation_operations causal_mutation_log.
proof.
  rewrite /bee_safe_kappa_mutated /beekem_mutated_all_challenges_safe
    /beekem_mutated_challenge_safe_against /beekem_mutated_pair_safe
    /beekem_mutated_fsu_clause /beekem_mutated_pcs_clause
    /beekem_mutated_cfs_clause /beekem_q2op_frontiers_differ
    /causal_mutation_log
    /beekem_kappa_fsu_clause /beekem_pcs_clause /beekem_kappa_cfs_clause
    /beekem_update_chain_between /beekem_update_chain_ending_at
    /beekem_successful_update_for /beekem_q2op_precedes
    /beekem_q2op_precedes_or_equals /beekem_q2op_concurrent
    /beekem_q2op_set /beekem_query_successful
    /beekem_query_is_send_update /beekem_query_is_challenge
    /beekem_query_is_compromise
    /causal_mutation_update_query /causal_mutation_compromise_query
    /causal_mutation_challenge_query /beekem_trace_query.
  rewrite (elems_fset1 causal_mutation_update_id)
    (elems_fset1 causal_mutation_challenge_id).
  rewrite /beekem_ids_precede_frontier /beekem_ids_precede_or_equal_frontier
    /beekem_id_precedes_some /beekem_id_precedes_or_equals_some
    /beekem_ids_pairwise_concurrent /beekem_id_concurrent_with_all
    /beekem_operation_ids_concurrent
    /beekem_operation_id_precedes /beekem_operation_id_precedes_or_equals
    /beekem_operation_id_known /causal_mutation_operations
    /causal_mutation_update_operation /causal_mutation_challenge_operation
    /beekem_trace_operation.
  smt(in_fset0 in_fset1).
qed.
