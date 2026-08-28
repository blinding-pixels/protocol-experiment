import Std

namespace CausalDagCgka

/-- Extensional equality for predicates. -/
theorem pred_ext {α : Type} {p q : α → Prop}
    (h : ∀ x, p x ↔ q x) : p = q := by
  funext x
  exact propext (h x)

/-- Pointwise union of predicates. -/
def predUnion {α : Type} (p q : α → Prop) : α → Prop :=
  fun x => p x ∨ q x

@[simp] theorem predUnion_apply {α : Type} (p q : α → Prop) (x : α) :
    predUnion p q x ↔ p x ∨ q x := Iff.rfl

theorem predUnion_comm {α : Type} (p q : α → Prop) :
    predUnion p q = predUnion q p := by
  apply pred_ext
  intro x
  constructor <;> intro h
  · cases h with
    | inl hp => exact Or.inr hp
    | inr hq => exact Or.inl hq
  · cases h with
    | inl hq => exact Or.inr hq
    | inr hp => exact Or.inl hp

theorem predUnion_assoc {α : Type} (p q r : α → Prop) :
    predUnion (predUnion p q) r = predUnion p (predUnion q r) := by
  apply pred_ext
  intro x
  constructor <;> intro h
  · cases h with
    | inl hpq =>
        cases hpq with
        | inl hp => exact Or.inl hp
        | inr hq => exact Or.inr (Or.inl hq)
    | inr hr => exact Or.inr (Or.inr hr)
  · cases h with
    | inl hp => exact Or.inl (Or.inl hp)
    | inr hqr =>
        cases hqr with
        | inl hq => exact Or.inl (Or.inr hq)
        | inr hr => exact Or.inr hr

theorem predUnion_idem {α : Type} (p : α → Prop) :
    predUnion p p = p := by
  apply pred_ext
  intro x
  constructor
  · intro h
    cases h with
    | inl hp => exact hp
    | inr hp => exact hp
  · intro hp
    exact Or.inl hp

theorem predUnion_empty_left {α : Type} (p : α → Prop) :
    predUnion (fun _ => False) p = p := by
  apply pred_ext
  intro x
  constructor
  · intro h
    cases h with
    | inl hf => exact False.elim hf
    | inr hp => exact hp
  · intro hp
    exact Or.inr hp

theorem predUnion_empty_right {α : Type} (p : α → Prop) :
    predUnion p (fun _ => False) = p := by
  rw [predUnion_comm]
  exact predUnion_empty_left p

end CausalDagCgka
