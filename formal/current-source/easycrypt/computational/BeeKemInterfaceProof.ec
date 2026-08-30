require import BeeKemTypes BeeKemQueryLog BeeKemProtocol BeeKemSafety.

(* Public closure for the executable Figure 8 oracle environment and the exact
   finite-kappa Figure 3 safety predicate.  Later checkpoints add checked trace
   characterizations, the hidden-bit game, primitive games, and the imported
   BeeKEM Theorem 1 boundary without changing these definitions. *)
print beekem_operation_precedes.
print beekem_operation_precedes_or_equals.
print beekem_operations_concurrent.
print beekem_secret_output_is_no_output.
print beekem_secret_output_is_value.
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
