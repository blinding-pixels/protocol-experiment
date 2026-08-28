require import UnauthorizedReduction MutationProofs.

(* Active Deliverable A checker entry point.  Every new unauthorized-game or
   reduction theorem is imported here while it is under development, so a red
   proof cannot be hidden behind the already-green general checkpoint. *)
print UnauthorizedReduction.witness_honest_not_unauthorized.
print HonestOperationContract.witness_honest_operation_accepted.
print MutationProofs.noncanonical_rejection_probability_one.
