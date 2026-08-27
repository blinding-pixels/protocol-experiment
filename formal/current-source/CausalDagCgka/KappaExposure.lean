import Std

namespace CausalDagCgka

/--
`canDecrypt i n` means that historical individual secret number `i`, if retained
at compromise time, can recover the challenge material associated with node `n`.
This is deliberately combinatorial: computational secrecy stays in BeeKEM's
security game rather than being weakened into a proposition in Lean.
-/
def KappaExposed {Node : Type} (canDecrypt : Nat → Node → Prop)
    (kappa : Nat) (node : Node) : Prop :=
  ∃ i, i < kappa ∧ canDecrypt i node

/-- Retaining more historical individual secrets can only enlarge exposure. -/
theorem kappaExposure_mono {Node : Type} (canDecrypt : Nat → Node → Prop)
    {small large : Nat} (hkl : small ≤ large) {node : Node} :
    KappaExposed canDecrypt small node → KappaExposed canDecrypt large node := by
  intro h
  rcases h with ⟨i, hi, hdec⟩
  exact ⟨i, Nat.lt_of_lt_of_le hi hkl, hdec⟩

/-- Equivalently, the set of protected challenge nodes shrinks as `kappa` grows. -/
theorem kappaProtection_antitone {Node : Type} (canDecrypt : Nat → Node → Prop)
    {small large : Nat} (hkl : small ≤ large) {node : Node} :
    (¬ KappaExposed canDecrypt large node) →
      (¬ KappaExposed canDecrypt small node) := by
  intro hProtected hSmall
  exact hProtected (kappaExposure_mono canDecrypt hkl hSmall)

/--
If every challenge node is recoverable from some historical individual secret,
then every fixed node eventually enters the exposure cone as retention grows.
This is the precise finite statement behind the warning that `kappa = infinity`
can make the admissible cross-fork challenge set empty for long-lived members.
-/
theorem eventually_exposed_under_unbounded_retention {Node : Type}
    (canDecrypt : Nat → Node → Prop)
    (hComplete : ∀ node, ∃ i, canDecrypt i node) :
    ∀ node, ∃ kappa, KappaExposed canDecrypt kappa node := by
  intro node
  rcases hComplete node with ⟨i, hi⟩
  exact ⟨i + 1, i, Nat.lt_succ_self i, hi⟩

/-- A node outside the larger exposure cone is outside every smaller cone. -/
theorem admissible_for_large_implies_admissible_for_small {Node : Type}
    (canDecrypt : Nat → Node → Prop) {small large : Nat}
    (hkl : small ≤ large) (node : Node)
    (hAdmissible : ¬ KappaExposed canDecrypt large node) :
    ¬ KappaExposed canDecrypt small node :=
  kappaProtection_antitone canDecrypt hkl hAdmissible

end CausalDagCgka
