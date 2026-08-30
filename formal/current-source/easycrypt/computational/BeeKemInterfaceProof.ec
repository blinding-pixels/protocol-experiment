require import BeeKemTypes BeeKemQueryLog BeeKemProtocol.

(* Public closure for the executable Figure 8 oracle environment.  Importing
   BeeKemProtocol checks the complete stateful oracle surface; later
   checkpoints add the exact safety predicate and hidden-bit game here. *)
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
