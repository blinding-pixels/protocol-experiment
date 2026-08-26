require import MutationProofs.

(* Milestone-only checker entry point. Importing MutationProofs forces the
   complete executable validator, mutation harness, and the proved
   non-vacuity obligations through the EasyCrypt kernel. *)
print noncanonical_rejection_probability_one.
