require import AllCore List FSet Distr.
require import BeeKemTypes BeeKemProtocol BeeKemKiGame BeeKemTheorem1Math.
require import BeeKemConstruction BeeKemGameWitnesses BeeKemBoundaryCounterexample.
require BeeKemKiInterface.
clone import BeeKemKiInterface as BKI.

(* QUARANTINED DIAGNOSTIC: never import this theory into production proofs.
   An accepted false goal here diagnoses an inconsistent imported boundary. *)
lemma imported_boundary_contradiction &m
    (group : beekem_group) (membership : beekem_dgm) : false.
proof.
  have Hbound := beekem_theorem1_imported_normalized
    BoundaryHiddenBitReader &m
    [beekem_witness_user] group 1 0 2 1 membership.
  have Hnike := boundary_nike_symmetry &m.
  have Hse := boundary_se_correctness &m.
  have Hsafe := boundary_nonempty_all_safe &m group membership.
  have Hcounter := boundary_nonempty_counters_zero &m group membership.
  have Hceil := beekem_ceil_log2_two.
  have Hbound' := Hbound _ _ Hceil Hnike Hse Hsafe Hcounter.
  + done.
  + done.
  elim Hbound' => BNike BSe Hbad.
  rewrite boundary_nonempty_advantage_half /beekem_theorem1_loss in Hbad.
  smt().
qed.
