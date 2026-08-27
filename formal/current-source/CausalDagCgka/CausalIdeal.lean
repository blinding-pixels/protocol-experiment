import Std

namespace CausalDagCgka

/-- A causal region is an ideal when membership is closed into the strict causal past. -/
def IsCausalIdeal {Node : Type} (before : Node → Node → Prop)
    (region : Node → Prop) : Prop :=
  ∀ ⦃earlier later : Node⦄, before earlier later → region later → region earlier

/-- A predicate over a linear index is prefix-closed. -/
def IsPrefixClosed (region : Nat → Prop) : Prop :=
  ∀ ⦃i j : Nat⦄, i ≤ j → region j → region i

/--
A completely concurrent history has no causal edges. Every subset of its nodes
is therefore a causal ideal. Consequently, restricting grants only to "causal
ideals" does not by itself rule out arbitrary subsets or imply compactness.
-/
theorem antichain_every_region_is_ideal {Node : Type}
    (region : Node → Prop) :
    IsCausalIdeal (fun _ _ => False) region := by
  intro earlier later hBefore hLater
  exact False.elim hBefore

/--
A segment embeds a linear sequence into the strict causal order. Strict index
inequality is used deliberately: the causal order is irreflexive, so requiring
`before (nodeAt i) (nodeAt i)` would make the model inconsistent.
-/
structure CausalSegment (Node : Type) where
  before : Node → Node → Prop
  nodeAt : Nat → Node
  monotone : ∀ ⦃i j : Nat⦄, i < j → before (nodeAt i) (nodeAt j)

/-- The intersection of a causal ideal with a causal-linear segment is a prefix. -/
theorem ideal_intersection_is_prefix {Node : Type}
    (segment : CausalSegment Node) (region : Node → Prop)
    (hIdeal : IsCausalIdeal segment.before region) :
    IsPrefixClosed (fun i => region (segment.nodeAt i)) := by
  intro i j hij hj
  by_cases hEq : i = j
  · subst j
    exact hj
  · have hLt : i < j := by omega
    exact hIdeal (segment.monotone hLt) hj

/--
The finite-index version used by a segment-local complete binary key tree.
It is the bridge from a DAG ideal to one dyadic-prefix capability per touched
segment.
-/
theorem finite_ideal_intersection_is_prefix {Node : Type} {n : Nat}
    (segment : CausalSegment Node) (region : Node → Prop)
    (hIdeal : IsCausalIdeal segment.before region)
    {i j : Fin n} (hij : i ≤ j) (hj : region (segment.nodeAt j.val)) :
    region (segment.nodeAt i.val) := by
  by_cases hValEq : i.val = j.val
  · have hEq : i = j := Fin.ext hValEq
    subst j
    exact hj
  · have hValLe : i.val ≤ j.val := hij
    have hValLt : i.val < j.val := by omega
    exact hIdeal (segment.monotone hValLt) hj

end CausalDagCgka
