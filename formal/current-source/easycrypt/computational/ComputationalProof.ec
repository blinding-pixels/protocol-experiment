require import HonestOperationContract MutationProofs.

(* Current checker entry point for the computational development.

   This file deliberately exposes only the claims that have already been
   discharged by the kernel.  In particular, it does not claim the final
   unauthorized-acceptance reduction, live-key indistinguishability, or
   content-key indistinguishability required by the handoff.

   The first print is the direct, non-vacuous production acceptance witness:
   the concrete canonical operation is accepted by the public validator with
   probability one.  The second print is a concrete negative control through
   that same validator. *)
print HonestOperationContract.witness_honest_operation_accepted.
print MutationProofs.noncanonical_rejection_probability_one.
