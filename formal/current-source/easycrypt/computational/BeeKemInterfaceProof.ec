require import BeeKemTypes BeeKemQueryLog.

(* Initial public closure for the BeeKEM workstream.  Later checkpoints extend
   this entry point; compiling it now ensures that the protocol and log carriers
   are accepted before any security premise is introduced. *)
print beekem_operation_precedes.
print beekem_operation_precedes_or_equals.
print beekem_operations_concurrent.
print beekem_query_is_send_update.
print beekem_query_is_challenge.
print beekem_query_is_compromise.
print beekem_query_successful.
