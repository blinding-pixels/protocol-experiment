import CausalDagCgka.Logic

namespace CausalDagCgka

/-- Public, authenticated puncture facts. Secret constrained-key states are not members. -/
abbrev PunctureSet (Index : Type) := Index → Prop

namespace PunctureSet

variable {Index Secret : Type}

/-- The only replicated merge is union of public puncture facts. -/
def join (p q : PunctureSet Index) : PunctureSet Index := predUnion p q

/-- A base capability can read `x` only when `x` has not been publicly punctured. -/
def readable (base : Index → Prop) (punctures : PunctureSet Index) (x : Index) : Prop :=
  base x ∧ ¬ punctures x

theorem join_comm (p q : PunctureSet Index) : join p q = join q p :=
  predUnion_comm p q

theorem join_assoc (p q r : PunctureSet Index) :
    join (join p q) r = join p (join q r) :=
  predUnion_assoc p q r

theorem join_idem (p : PunctureSet Index) : join p p = p :=
  predUnion_idem p

/-- T4, at the public-state level: applying puncture regions commutes. -/
theorem concurrent_punctures_commute (base p q : PunctureSet Index) :
    join (join base p) q = join (join base q) p := by
  rw [join_assoc, join_assoc]
  rw [join_comm p q]

/-- No-resurrection: every fact in either input remains punctured after merge. -/
theorem no_resurrection
    (base : Index → Prop) (p q : PunctureSet Index) (x : Index)
    (hx : join p q x) :
    ¬ readable base (join p q) x := by
  intro hReadable
  exact hReadable.2 hx

/-- Adding punctures can only remove readability. -/
theorem readability_monotone
    (base : Index → Prop) (p q : PunctureSet Index) (x : Index) :
    readable base (join p q) x → readable base p x := by
  intro h
  constructor
  · exact h.1
  · intro hp
    exact h.2 (Or.inl hp)

/--
The secret capability is deliberately an external argument to `readable`.
There is therefore no operation in this model that unions two constrained
secret states; only authenticated public tombstones join.
-/
theorem merged_public_state_cannot_restore
    (base : Index → Prop) (p q : PunctureSet Index) (x : Index)
    (hp : p x) :
    ¬ readable base (join p q) x := by
  apply no_resurrection base p q x
  exact Or.inl hp

end PunctureSet

end CausalDagCgka
