import CausalDagCgka.KappaExposure

namespace CausalDagCgka

/--
The content-key exposure region at a compromise point.

- `canDecrypt` and `kappa` model BeeKEM's retained-personal-secret cone;
- `retainedHistory` models unresolved export capabilities kept for future grants;
- `grantedToCorrupt` models regions already granted to corrupted principals.
-/
def ContentExposed {Node Index : Type}
    (canDecrypt : Nat → Node → Prop) (kappa : Nat) (challengeNode : Node)
    (retainedHistory grantedToCorrupt : Index → Prop) (index : Index) : Prop :=
  KappaExposed canDecrypt kappa challengeNode ∨
  retainedHistory index ∨
  grantedToCorrupt index

/-- A content-key challenge is admissible exactly outside the total exposure region. -/
def ContentChallengeAdmissible {Node Index : Type}
    (canDecrypt : Nat → Node → Prop) (kappa : Nat) (challengeNode : Node)
    (retainedHistory grantedToCorrupt : Index → Prop) (index : Index) : Prop :=
  ¬ ContentExposed canDecrypt kappa challengeNode retainedHistory grantedToCorrupt index

/-- Increasing BeeKEM retention can only enlarge total exposure. -/
theorem contentExposure_mono_kappa {Node Index : Type}
    (canDecrypt : Nat → Node → Prop) {small large : Nat} (hkl : small ≤ large)
    (challengeNode : Node) (retainedHistory grantedToCorrupt : Index → Prop)
    (index : Index) :
    ContentExposed canDecrypt small challengeNode retainedHistory grantedToCorrupt index →
    ContentExposed canDecrypt large challengeNode retainedHistory grantedToCorrupt index := by
  intro h
  cases h with
  | inl hk =>
      exact Or.inl (kappaExposure_mono canDecrypt hkl hk)
  | inr hhg =>
      exact Or.inr hhg

/-- Removing retained-history coverage cannot create a new exposure. -/
theorem erase_history_shrinks_exposure {Node Index : Type}
    (canDecrypt : Nat → Node → Prop) (kappa : Nat) (challengeNode : Node)
    (before after grantedToCorrupt : Index → Prop)
    (hErase : ∀ i, after i → before i) (index : Index) :
    ContentExposed canDecrypt kappa challengeNode after grantedToCorrupt index →
    ContentExposed canDecrypt kappa challengeNode before grantedToCorrupt index := by
  intro h
  cases h with
  | inl hk => exact Or.inl hk
  | inr hhg =>
      cases hhg with
      | inl hh => exact Or.inr (Or.inl (hErase index hh))
      | inr hg => exact Or.inr (Or.inr hg)

/--
After all three exposure sources are absent, the challenge lies outside the
combinatorial exposure region. This is the exact precondition consumed by the
computational post-erasure theorem; Lean does not turn it into negligible
adversarial advantage.
-/
theorem admissible_when_unexposed {Node Index : Type}
    (canDecrypt : Nat → Node → Prop) (kappa : Nat) (challengeNode : Node)
    (retainedHistory grantedToCorrupt : Index → Prop) (index : Index)
    (hKappa : ¬ KappaExposed canDecrypt kappa challengeNode)
    (hRetained : ¬ retainedHistory index)
    (hGranted : ¬ grantedToCorrupt index) :
    ContentChallengeAdmissible canDecrypt kappa challengeNode
      retainedHistory grantedToCorrupt index := by
  intro hExposed
  cases hExposed with
  | inl hk => exact hKappa hk
  | inr hhg =>
      cases hhg with
      | inl hh => exact hRetained hh
      | inr hg => exact hGranted hg

/-- A challenge admissible for a larger `kappa` is admissible for every smaller one. -/
theorem admissibility_antitone_kappa {Node Index : Type}
    (canDecrypt : Nat → Node → Prop) {small large : Nat} (hkl : small ≤ large)
    (challengeNode : Node) (retainedHistory grantedToCorrupt : Index → Prop)
    (index : Index) :
    ContentChallengeAdmissible canDecrypt large challengeNode
      retainedHistory grantedToCorrupt index →
    ContentChallengeAdmissible canDecrypt small challengeNode
      retainedHistory grantedToCorrupt index := by
  intro hLarge hSmallExposed
  exact hLarge
    (contentExposure_mono_kappa canDecrypt hkl challengeNode
      retainedHistory grantedToCorrupt index hSmallExposed)

end CausalDagCgka
