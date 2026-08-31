require import AllCore List FSet Distr.
require import BeeKemTypes BeeKemQueryLog BeeKemProtocol BeeKemSafety.
require import BeeKemKiGame BeeKemGameWitnesses BeeKemMutationGameProofs.

(* Use the exact Figure-8 game and the existing FSU exposure adversary.  The
   trace executes Create -> Update -> Challenge -> Compromise.  Its challenge
   is real and counted, but the complete authoritative log is unsafe for every
   hidden bit, so the exact game must lose rather than gain half an advantage. *)
module BeeKemUnsafeNormalizationGame =
  BeeKemKiGame(
    BeeKemFsuExposureAdversary,
    BeeKemWitnessProtocol
  ).

lemma beekem_unsafe_normalization_fixed_bit_loses :
  hoare [BeeKemUnsafeNormalizationGame.main_with_fixed_bit :
       users = [beekem_witness_user]
    /\ group = beekem_witness_group
    /\ kappa = 1
    /\ membership = beekem_witness_membership
    ==>
       res.`bke_challenge_count = 1
    /\ ! res.`bke_safe
    /\ ! res.`bke_win].
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
    /beekem_query_is_compromise /beekem_ki_final_win.
  rewrite (elems_fset1 beekem_witness_create_id)
    (elems_fset1 beekem_witness_update_id).
  smt(in_fset0 in_fset1 size_rcons size_ge0).
qed.

lemma beekem_unsafe_normalization_sampled_game_loses :
  hoare [BeeKemUnsafeNormalizationGame.main_with_evidence :
       users = [beekem_witness_user]
    /\ group = beekem_witness_group
    /\ kappa = 1
    /\ membership = beekem_witness_membership
    ==>
       res.`bke_challenge_count = 1
    /\ ! res.`bke_safe
    /\ ! res.`bke_win].
proof.
  proc.
  call beekem_unsafe_normalization_fixed_bit_loses.
  auto.
qed.

lemma beekem_unsafe_normalization_main_never_wins :
  hoare [BeeKemUnsafeNormalizationGame.main :
       users = [beekem_witness_user]
    /\ group = beekem_witness_group
    /\ kappa = 1
    /\ membership = beekem_witness_membership
    ==>
       ! res].
proof.
  proc.
  call beekem_unsafe_normalization_sampled_game_loses.
  auto.
qed.

lemma beekem_unsafe_normalization_win_probability_zero &m :
  Pr[
    BeeKemUnsafeNormalizationGame.main(
      [beekem_witness_user],
      beekem_witness_group,
      1,
      beekem_witness_membership
    ) @ &m : res
  ] = 0%r.
proof.
  byphoare
    (_ :
       users = [beekem_witness_user]
    /\ group = beekem_witness_group
    /\ kappa = 1
    /\ membership = beekem_witness_membership
    ==> ! res) => //=.
  exact beekem_unsafe_normalization_main_never_wins.
qed.

lemma beekem_unsafe_normalization_safe_probability_zero &m :
  Pr[
    BeeKemUnsafeNormalizationGame.main_with_evidence(
      [beekem_witness_user],
      beekem_witness_group,
      1,
      beekem_witness_membership
    ) @ &m : res.`bke_safe
  ] = 0%r.
proof.
  byphoare
    (_ :
       users = [beekem_witness_user]
    /\ group = beekem_witness_group
    /\ kappa = 1
    /\ membership = beekem_witness_membership
    ==> ! res.`bke_safe) => //=.
  conseq beekem_unsafe_normalization_sampled_game_loses => //.
qed.

(* This is the exact old bug: centering the aborted win probability around an
   unconditional half gives a spurious half advantage. *)
lemma beekem_unsafe_trace_old_normalization_is_spurious_half &m :
  beekem_normalized_ki_advantage
    (Pr[
       BeeKemUnsafeNormalizationGame.main(
         [beekem_witness_user],
         beekem_witness_group,
         1,
         beekem_witness_membership
       ) @ &m : res
     ]) = 1%r / 2%r.
proof.
  rewrite beekem_unsafe_normalization_win_probability_zero.
  rewrite /beekem_normalized_ki_advantage.
  by smt().
qed.

lemma beekem_unsafe_trace_safe_mass_advantage_zero &m :
  beekem_safe_mass_normalized_ki_advantage
    (Pr[
       BeeKemUnsafeNormalizationGame.main(
         [beekem_witness_user],
         beekem_witness_group,
         1,
         beekem_witness_membership
       ) @ &m : res
     ])
    (Pr[
       BeeKemUnsafeNormalizationGame.main_with_evidence(
         [beekem_witness_user],
         beekem_witness_group,
         1,
         beekem_witness_membership
       ) @ &m : res.`bke_safe
     ]) = 0%r.
proof.
  rewrite beekem_unsafe_normalization_win_probability_zero
    beekem_unsafe_normalization_safe_probability_zero.
  exact beekem_safe_mass_normalization_zero.
qed.

(* The same executable unsafe trace cannot discharge the imported theorem's
   all-safe side condition.  Final application composition must prove that side
   condition from the authoritative adapter and complete query log. *)
lemma beekem_unsafe_trace_rejected_by_all_safe_boundary &m :
  Pr[
    BeeKemUnsafeNormalizationGame.main_with_evidence(
      [beekem_witness_user],
      beekem_witness_group,
      1,
      beekem_witness_membership
    ) @ &m : res.`bke_safe
  ] <> 1%r.
proof.
  rewrite beekem_unsafe_normalization_safe_probability_zero.
  by smt().
qed.
