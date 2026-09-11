require import AllCore BeeKemBoundaryCounterexample.

(* Negative control: this attempted contradiction must be rejected. *)
lemma boundary_no_axiom_false : false.
proof. smt(). qed.
