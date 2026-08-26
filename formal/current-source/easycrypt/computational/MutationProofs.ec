require import AllCore List FSet.
require import MutationWitnesses.

(* First checker-driven non-vacuity obligation.  This executes the same
   NormalizeAuthorization and ValidateOperation procedures imported by the
   production unauthorized-acceptance game. *)
lemma noncanonical_rejection_probability_one &m :
  Pr[NonCanonicalRejectionWitness.main() @ &m : res] = 1%r.
proof.
  byphoare=> //.
  proc.
  inline *.
  auto.
qed.
