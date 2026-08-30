require import AllCore List FSet.
require import BeeKemTypes BeeKemQueryLog BeeKemProtocol BeeKemSafety.
require import BeeKemKiGame BeeKemGameWitnesses BeeKemSafetyMutations.
require import BeeKemMutationGameProofs BeeKemForkGameWitnesses.

module BeeKemCfsForkMutationGame =
  BeeKemSafetyMutationGame(
    BeeKemCfsForkExposureAdversary,
    BeeKemForkWitnessProtocol
  ).

module BeeKemCausalAncestryMutationGame =
  BeeKemSafetyMutationGame(
    BeeKemCausalAncestryExposureAdversary,
    BeeKemForkWitnessProtocol
  ).

lemma mutation_cfs_chain_reaches_actual_ki_game :
  hoare [BeeKemCfsForkMutationGame.main_with_fixed_mutation :
       users = [beekem_witness_user]
    /\ group = beekem_witness_group
    /\ kappa = 2
    /\ membership = beekem_witness_membership
    /\ hidden_bit = true
    /\ mutation = BeeMutationDropCfsUpdateChain
    ==>
       res.`bmge_hidden_bit
    /\ res.`bmge_adversary_guess
    /\ ! res.`bmge_protocol_consistency_failure
    /\ res.`bmge_challenge_count = 1
    /\ res.`bmge_member_addition_count = 0
    /\ ! res.`bmge_exact_safe
    /\ ! res.`bmge_exact_win
    /\ res.`bmge_mutated_safe
    /\ res.`bmge_mutated_win].
proof.
  proc.
  inline *.
  rcondt ^while; first by auto.
  rcondf ^while; first by auto.
  rcondf ^while; first by auto.
  rcondt ^while; first by auto.
  rcondf ^while; first by auto.
  rcondf ^while; first by auto.
  rcondt ^while; first by auto.
  rcondf ^while; first by auto.
  rcondf ^while; first by auto.
  auto.
  rewrite /beekem_witness_membership /beekem_witness_initial_member_state
    /beekem_member_retention_valid /beekem_witness_personal_secret
    /beekem_witness_after_create /beekem_witness_after_update
    /beekem_fork_after_second_update
    /beekem_witness_control /beekem_witness_create_operation
    /beekem_witness_update_operation /beekem_fork_second_update_operation
    /beekem_witness_operation
    /beekem_control_operation_id /beekem_control_operation
    /beekem_counter_value /beekem_empty_protocol_state
    /beekem_secret_output_is_undefined /beekem_secret_output_is_value
    /beekem_secret_output_value /beekem_operation_precedes_or_equals
    /beekem_operation_precedes /bee_safe_kappa /beekem_all_challenges_safe
    /beekem_challenge_safe_against /beekem_challenge_compromise_pair_safe
    /beekem_kappa_fsu_clause /beekem_pcs_clause /beekem_kappa_cfs_clause
    /beekem_update_chain_between /beekem_update_chain_ending_at
    /beekem_successful_update_for /beekem_q2op_precedes
    /beekem_q2op_precedes_or_equals /beekem_q2op_concurrent
    /beekem_q2op_set /beekem_ids_precede_frontier
    /beekem_ids_precede_or_equal_frontier /beekem_id_precedes_some
    /beekem_id_precedes_or_equals_some /beekem_ids_pairwise_concurrent
    /beekem_id_concurrent_with_all /beekem_operation_ids_concurrent
    /beekem_operation_id_precedes /beekem_operation_id_precedes_or_equals
    /beekem_operation_id_known /beekem_query_successful
    /beekem_query_is_send_update /beekem_query_is_challenge
    /beekem_query_is_compromise /bee_safe_kappa_mutated
    /beekem_mutated_all_challenges_safe
    /beekem_mutated_challenge_safe_against /beekem_mutated_pair_safe
    /beekem_mutated_fsu_clause /beekem_mutated_pcs_clause
    /beekem_mutated_cfs_clause /beekem_q2op_frontiers_differ
    /beekem_ki_final_win.
  rewrite (elems_fset1 beekem_witness_create_id)
    (elems_fset1 beekem_witness_update_id)
    (elems_fset1 beekem_fork_second_update_id).
  smt(in_fset0 in_fset1 in_fsetU size_rcons size_ge0).
qed.

lemma mutation_ignore_ancestry_reaches_actual_ki_game :
  hoare [BeeKemCausalAncestryMutationGame.main_with_fixed_mutation :
       users = [beekem_witness_user]
    /\ group = beekem_witness_group
    /\ kappa = 1
    /\ membership = beekem_witness_membership
    /\ hidden_bit = true
    /\ mutation = BeeMutationIgnoreCausalAncestry
    ==>
       res.`bmge_hidden_bit
    /\ res.`bmge_adversary_guess
    /\ ! res.`bmge_protocol_consistency_failure
    /\ res.`bmge_challenge_count = 1
    /\ res.`bmge_member_addition_count = 1
    /\ ! res.`bmge_exact_safe
    /\ ! res.`bmge_exact_win
    /\ res.`bmge_mutated_safe
    /\ res.`bmge_mutated_win].
proof.
  proc.
  inline *.
  rcondt ^while; first by auto.
  rcondf ^while; first by auto.
  rcondf ^while; first by auto.
  rcondt ^while; first by auto.
  rcondf ^while; first by auto.
  rcondf ^while; first by auto.
  rcondt ^while; first by auto.
  rcondf ^while; first by auto.
  rcondf ^while; first by auto.
  auto.
  rewrite /beekem_witness_membership /beekem_witness_initial_member_state
    /beekem_member_retention_valid /beekem_witness_personal_secret
    /beekem_witness_after_create /beekem_witness_after_update
    /beekem_fork_after_causal_add
    /beekem_witness_control /beekem_witness_create_operation
    /beekem_witness_update_operation /beekem_fork_causal_add_operation
    /beekem_witness_operation /beekem_fork_add_target
    /beekem_control_operation_id /beekem_control_operation
    /beekem_counter_value /beekem_empty_protocol_state
    /beekem_secret_output_is_undefined /beekem_secret_output_is_value
    /beekem_secret_output_value /beekem_operation_precedes_or_equals
    /beekem_operation_precedes /bee_safe_kappa /beekem_all_challenges_safe
    /beekem_challenge_safe_against /beekem_challenge_compromise_pair_safe
    /beekem_kappa_fsu_clause /beekem_pcs_clause /beekem_kappa_cfs_clause
    /beekem_update_chain_between /beekem_update_chain_ending_at
    /beekem_successful_update_for /beekem_q2op_precedes
    /beekem_q2op_precedes_or_equals /beekem_q2op_concurrent
    /beekem_q2op_set /beekem_ids_precede_frontier
    /beekem_ids_precede_or_equal_frontier /beekem_id_precedes_some
    /beekem_id_precedes_or_equals_some /beekem_ids_pairwise_concurrent
    /beekem_id_concurrent_with_all /beekem_operation_ids_concurrent
    /beekem_operation_id_precedes /beekem_operation_id_precedes_or_equals
    /beekem_operation_id_known /beekem_query_successful
    /beekem_query_is_send_update /beekem_query_is_challenge
    /beekem_query_is_compromise /bee_safe_kappa_mutated
    /beekem_mutated_all_challenges_safe
    /beekem_mutated_challenge_safe_against /beekem_mutated_pair_safe
    /beekem_mutated_fsu_clause /beekem_mutated_pcs_clause
    /beekem_mutated_cfs_clause /beekem_q2op_frontiers_differ
    /beekem_ki_final_win.
  rewrite (elems_fset1 beekem_witness_create_id)
    (elems_fset1 beekem_witness_update_id)
    (elems_fset1 beekem_fork_causal_add_id).
  smt(in_fset0 in_fset1 in_fsetU size_rcons size_ge0).
qed.
