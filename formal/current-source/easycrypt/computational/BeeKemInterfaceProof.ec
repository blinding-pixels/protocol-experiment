require import BeeKemTypes BeeKemQueryLog BeeKemProtocol BeeKemSafety BeeKemKiGame.
require import BeeKemSafetyProofs BeeKemProtocolSemanticsProofs.

(* Public closure for the executable Figure 8 oracle environment and exact
   finite-kappa Figure 3 safety predicate.  The trace theorems below force all
   three safety disjuncts and their unsafe boundaries to compute. *)
print beekem_operation_precedes.
print beekem_operation_precedes_or_equals.
print beekem_operations_concurrent.
print beekem_secret_output_is_no_output.
print beekem_secret_output_is_undefined.
print beekem_secret_output_is_value.
print beekem_member_retention_valid.
print beekem_empty_protocol_state.
print beekem_query_is_send_update.
print beekem_query_is_challenge.
print beekem_query_is_compromise.
print beekem_query_successful.
print beekem_control_operation.
print beekem_control_operation_id.
print beekem_counter_value.
print beekem_q2op_set.
print beekem_q2op_precedes.
print beekem_q2op_precedes_or_equals.
print beekem_q2op_concurrent.
print beekem_kappa_fsu_clause.
print beekem_pcs_clause.
print beekem_kappa_cfs_clause.
print beekem_challenge_compromise_pair_safe.
print bee_safe_kappa.
print fsu_positive_uses_fsu_clause.
print pcs_positive_uses_pcs_clause.
print cfs_positive_uses_cfs_clause.
print fsu_trace_admissible_at_kappa_three.
print fsu_kappa_one_boundary_admitted.
print fsu_kappa_two_boundary_rejected.
print fsu_larger_finite_window_rejected_at_four.
print pcs_trace_admissible.
print pcs_trace_without_healing_update_rejected.
print cfs_trace_admissible_at_kappa_two.
print cfs_trace_without_fork_updates_rejected.

print beekem_no_output_is_not_undefined.
print beekem_undefined_is_not_no_output.
print beekem_value_is_not_undefined.
print beekem_empty_secret_entry_is_undefined.
print beekem_retention_requires_positive_kappa.

(* KI-DCGKA public game boundary.  Importing BeeKemKiGame checks the hidden-bit
   challenger, the complete adversary oracle interface, and use of the final
   adversary guess. *)
print beekem_ki_evidence.
print beekem_normalized_ki_advantage.
