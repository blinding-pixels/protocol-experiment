require import AllCore List FSet.
require import BeeKemTypes BeeKemQueryLog BeeKemProtocol BeeKemSafety.
require import BeeKemKiGame BeeKemGameWitnesses BeeKemSafetyMutations.

(* The mutation harness first executes the exact KI-DCGKA game, including its
   real oracle state and query log.  It then changes only the named final safety
   predicate and recomputes the win bit through [beekem_ki_final_win]. *)
type beekem_mutation_game_evidence = {
  bmge_hidden_bit : bool;
  bmge_adversary_guess : bool;
  bmge_protocol_consistency_failure : bool;
  bmge_challenge_count : int;
  bmge_member_addition_count : int;
  bmge_exact_safe : bool;
  bmge_exact_win : bool;
  bmge_mutated_safe : bool;
  bmge_mutated_win : bool
}.

module BeeKemSafetyMutationGame(
  A : BEEKEM_KI_ADVERSARY,
  P : BEEKEM_PROTOCOL_ALGORITHMS,
  R : BEEKEM_GROUP_SECRET_SAMPLER
) = {
  module Exact = BeeKemKiGame(A, P, R)

  proc main_with_fixed_mutation(
    users : beekem_user list,
    group : beekem_group,
    kappa : int,
    membership : beekem_dgm,
    hidden_bit : bool,
    mutation : beekem_safety_mutation
  ) : beekem_mutation_game_evidence = {
    var exact : beekem_ki_evidence;
    var mutated_safe : bool;
    var mutated_win : bool;

    exact <@ Exact.main_with_fixed_bit(
      users, group, kappa, membership, hidden_bit
    );
    mutated_safe <- bee_safe_kappa_mutated
      mutation
      kappa
      Exact.O.Environment.state.`bps_operations
      Exact.O.Environment.query_log;
    mutated_win <- beekem_ki_final_win
      mutated_safe
      exact.`bke_protocol_consistency_failure
      exact.`bke_adversary_guess
      hidden_bit;

    return
      {| bmge_hidden_bit = exact.`bke_hidden_bit;
         bmge_adversary_guess = exact.`bke_adversary_guess;
         bmge_protocol_consistency_failure =
           exact.`bke_protocol_consistency_failure;
         bmge_challenge_count = exact.`bke_challenge_count;
         bmge_member_addition_count = exact.`bke_member_addition_count;
         bmge_exact_safe = exact.`bke_safe;
         bmge_exact_win = exact.`bke_win;
         bmge_mutated_safe = mutated_safe;
         bmge_mutated_win = mutated_win |};
  }
}.

module BeeKemFsuExposureAdversary(O : BEEKEM_KI_ORACLES) = {
  proc attack() : bool = {
    var created : bool;
    var updated : bool;
    var answer : beekem_secret_output;
    var compromised : beekem_member_state option;

    created <@ O.create_group(beekem_witness_user, fset0);
    updated <@ O.send_update(beekem_witness_user);
    answer <@ O.challenge(beekem_witness_user, BeeKemCounter 2);
    compromised <@ O.compromise(beekem_witness_user);
    return created /\ updated /\ compromised <> None /\
      answer = BeeSecretValue beekem_witness_real_secret;
  }
}.

module BeeKemPcsExposureAdversary(O : BEEKEM_KI_ORACLES) = {
  proc attack() : bool = {
    var created : bool;
    var updated : bool;
    var compromised : beekem_member_state option;
    var answer : beekem_secret_output;

    created <@ O.create_group(beekem_witness_user, fset0);
    updated <@ O.send_update(beekem_witness_user);
    compromised <@ O.compromise(beekem_witness_user);
    answer <@ O.challenge(beekem_witness_user, BeeKemCounter 2);
    return created /\ updated /\ compromised <> None /\
      answer = BeeSecretValue beekem_witness_real_secret;
  }
}.

module BeeKemFsuExposureMutationGame =
  BeeKemSafetyMutationGame(
    BeeKemFsuExposureAdversary,
    BeeKemWitnessProtocol,
    BeeKemWitnessSecretSampler
  ).

module BeeKemPcsExposureMutationGame =
  BeeKemSafetyMutationGame(
    BeeKemPcsExposureAdversary,
    BeeKemWitnessProtocol,
    BeeKemWitnessSecretSampler
  ).

lemma mutation_fsu_chain_reaches_actual_ki_game :
  hoare [BeeKemFsuExposureMutationGame.main_with_fixed_mutation :
       users = [beekem_witness_user]
    /\ group = beekem_witness_group
    /\ kappa = 1
    /\ membership = beekem_witness_membership
    /\ hidden_bit = true
    /\ mutation = BeeMutationDropFsuUpdateChain
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
  auto.
  rewrite /beekem_witness_membership /beekem_witness_initial_member_state
    /beekem_member_retention_valid /beekem_witness_personal_secret
    /beekem_witness_after_create /beekem_witness_after_update
    /beekem_witness_control /beekem_witness_create_operation
    /beekem_witness_update_operation /beekem_witness_operation
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
    (elems_fset1 beekem_witness_update_id).
  smt(in_fset0 in_fset1 size_rcons size_ge0).
qed.

lemma mutation_pcs_update_reaches_actual_ki_game :
  hoare [BeeKemPcsExposureMutationGame.main_with_fixed_mutation :
       users = [beekem_witness_user]
    /\ group = beekem_witness_group
    /\ kappa = 1
    /\ membership = beekem_witness_membership
    /\ hidden_bit = true
    /\ mutation = BeeMutationDropPcsHealingUpdate
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
  auto.
  rewrite /beekem_witness_membership /beekem_witness_initial_member_state
    /beekem_member_retention_valid /beekem_witness_personal_secret
    /beekem_witness_after_create /beekem_witness_after_update
    /beekem_witness_control /beekem_witness_create_operation
    /beekem_witness_update_operation /beekem_witness_operation
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
    (elems_fset1 beekem_witness_update_id).
  smt(in_fset0 in_fset1 size_rcons size_ge0).
qed.

lemma mutation_compromise_log_reaches_actual_ki_game :
  hoare [BeeKemFsuExposureMutationGame.main_with_fixed_mutation :
       users = [beekem_witness_user]
    /\ group = beekem_witness_group
    /\ kappa = 1
    /\ membership = beekem_witness_membership
    /\ hidden_bit = true
    /\ mutation = BeeMutationIgnoreCompromiseLog
    ==>
       res.`bmge_hidden_bit
    /\ res.`bmge_adversary_guess
    /\ ! res.`bmge_protocol_consistency_failure
    /\ res.`bmge_challenge_count = 1
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
  auto.
  rewrite /beekem_witness_membership /beekem_witness_initial_member_state
    /beekem_member_retention_valid /beekem_witness_personal_secret
    /beekem_witness_after_create /beekem_witness_after_update
    /beekem_witness_control /beekem_witness_create_operation
    /beekem_witness_update_operation /beekem_witness_operation
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
    (elems_fset1 beekem_witness_update_id).
  smt(in_fset0 in_fset1 size_rcons size_ge0).
qed.
