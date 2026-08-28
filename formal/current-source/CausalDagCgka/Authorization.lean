import CausalDagCgka.Logic

namespace CausalDagCgka

/--
An observed-remove authorization state. `added item tag` records an immutable
add fact with unique tag `tag`; `removed tag` records an immutable tombstone.
The protocol must validate each event against its signed causal past before its
immutable delta enters this state.
-/
structure AuthState (Item Tag : Type) where
  added : Item → Tag → Prop
  removed : Tag → Prop

namespace AuthState

variable {Item Tag : Type}

/-- Empty observed-remove state. -/
def empty : AuthState Item Tag where
  added := fun _ _ => False
  removed := fun _ => False

/-- State-based CRDT join: immutable facts are unioned componentwise. -/
def join (a b : AuthState Item Tag) : AuthState Item Tag where
  added := fun item tag => a.added item tag ∨ b.added item tag
  removed := fun tag => a.removed tag ∨ b.removed tag

/-- Extensional equality for observed-remove states. -/
theorem ext {a b : AuthState Item Tag}
    (hAdded : ∀ item tag, a.added item tag ↔ b.added item tag)
    (hRemoved : ∀ tag, a.removed tag ↔ b.removed tag) : a = b := by
  cases a with
  | mk aa ar =>
      cases b with
      | mk ba br =>
          have ha : aa = ba := by
            funext item tag
            exact propext (hAdded item tag)
          have hr : ar = br := by
            funext tag
            exact propext (hRemoved tag)
          cases ha
          cases hr
          rfl

@[simp] theorem join_added (a b : AuthState Item Tag) (item : Item) (tag : Tag) :
    (join a b).added item tag ↔ a.added item tag ∨ b.added item tag := Iff.rfl

@[simp] theorem join_removed (a b : AuthState Item Tag) (tag : Tag) :
    (join a b).removed tag ↔ a.removed tag ∨ b.removed tag := Iff.rfl

theorem join_comm (a b : AuthState Item Tag) : join a b = join b a := by
  apply ext
  · intro item tag
    exact Iff.intro
      (fun h => Or.elim h Or.inr Or.inl)
      (fun h => Or.elim h Or.inr Or.inl)
  · intro tag
    exact Iff.intro
      (fun h => Or.elim h Or.inr Or.inl)
      (fun h => Or.elim h Or.inr Or.inl)

theorem join_assoc (a b c : AuthState Item Tag) :
    join (join a b) c = join a (join b c) := by
  apply ext
  · intro item tag
    constructor
    · intro h
      cases h with
      | inl hab =>
          cases hab with
          | inl ha => exact Or.inl ha
          | inr hb => exact Or.inr (Or.inl hb)
      | inr hc => exact Or.inr (Or.inr hc)
    · intro h
      cases h with
      | inl ha => exact Or.inl (Or.inl ha)
      | inr hbc =>
          cases hbc with
          | inl hb => exact Or.inl (Or.inr hb)
          | inr hc => exact Or.inr hc
  · intro tag
    constructor
    · intro h
      cases h with
      | inl hab =>
          cases hab with
          | inl ha => exact Or.inl ha
          | inr hb => exact Or.inr (Or.inl hb)
      | inr hc => exact Or.inr (Or.inr hc)
    · intro h
      cases h with
      | inl ha => exact Or.inl (Or.inl ha)
      | inr hbc =>
          cases hbc with
          | inl hb => exact Or.inl (Or.inr hb)
          | inr hc => exact Or.inr hc

theorem join_idem (a : AuthState Item Tag) : join a a = a := by
  apply ext
  · intro item tag
    constructor
    · intro h
      exact Or.elim h id id
    · intro h
      exact Or.inl h
  · intro tag
    constructor
    · intro h
      exact Or.elim h id id
    · intro h
      exact Or.inl h

theorem join_empty_left (a : AuthState Item Tag) : join empty a = a := by
  apply ext
  · intro item tag
    constructor
    · intro h
      cases h with
      | inl hf => exact False.elim hf
      | inr ha => exact ha
    · intro ha
      exact Or.inr ha
  · intro tag
    constructor
    · intro h
      cases h with
      | inl hf => exact False.elim hf
      | inr ha => exact ha
    · intro ha
      exact Or.inr ha

theorem join_empty_right (a : AuthState Item Tag) : join a empty = a := by
  rw [join_comm]
  exact join_empty_left a

/-- An item is active iff some add-tag for it is not tombstoned. -/
def active (s : AuthState Item Tag) (item : Item) : Prop :=
  ∃ tag, s.added item tag ∧ ¬ s.removed tag

/-- An immutable add delta. -/
def addDelta (item : Item) (tag : Tag) : AuthState Item Tag where
  added := fun candidate candidateTag => candidate = item ∧ candidateTag = tag
  removed := fun _ => False

/-- An observed-remove delta tombstones exactly the tags in `observed`. -/
def removeObservedDelta (observed : Tag → Prop) : AuthState Item Tag where
  added := fun _ _ => False
  removed := observed

/-- Apply a validated immutable delta. -/
def applyDelta (s d : AuthState Item Tag) : AuthState Item Tag := join s d

/-- Apply a list of already-validated immutable deltas. -/
def applyAll : AuthState Item Tag → List (AuthState Item Tag) → AuthState Item Tag
  | s, [] => s
  | s, d :: ds => applyAll (applyDelta s d) ds

/-- Adjacent concurrent deltas commute. -/
theorem applyAll_swap (s a b : AuthState Item Tag)
    (rest : List (AuthState Item Tag)) :
    applyAll s (a :: b :: rest) = applyAll s (b :: a :: rest) := by
  have h : join (join s a) b = join (join s b) a := by
    rw [join_assoc, join_assoc]
    rw [join_comm a b]
  exact congrArg (fun state => applyAll state rest) h

/--
Observed-remove confluence: once event validity is fixed by each event's signed
causal context, replay order cannot change the normalized state. Any two
enumerations of the same immutable deltas converge.
-/
theorem applyAll_perm {xs ys : List (AuthState Item Tag)}
    (h : xs.Perm ys) (s : AuthState Item Tag) :
    applyAll s xs = applyAll s ys := by
  induction h generalizing s with
  | nil => rfl
  | cons x h ih =>
      exact ih (applyDelta s x)
  | swap x y rest =>
      exact applyAll_swap s y x rest
  | trans h₁ h₂ ih₁ ih₂ =>
      exact (ih₁ s).trans (ih₂ s)

/-- A concurrent fresh add-tag survives a remove that did not observe it. -/
theorem fresh_add_survives_observed_remove
    (item : Item) (oldTag newTag : Tag) (hFresh : newTag ≠ oldTag) :
    active
      (join (addDelta item newTag)
        (removeObservedDelta (fun tag => tag = oldTag)))
      item := by
  refine ⟨newTag, ?_, ?_⟩
  · exact Or.inl ⟨rfl, rfl⟩
  · intro hRemoved
    cases hRemoved with
    | inl hFalse => exact False.elim hFalse
    | inr hEqual => exact hFresh hEqual

/-- A remove that observed an add-tag makes that particular tag unusable. -/
theorem observed_tag_is_tombstoned
    (item : Item) (tag : Tag) :
    (join (addDelta item tag)
      (removeObservedDelta (fun candidate => candidate = tag))).removed tag := by
  exact Or.inr rfl

/-- If the only grant tag is observed by a remove, that item is inactive. -/
theorem observed_only_tag_is_inactive (item : Item) (tag : Tag) :
    ¬ active
      (join (addDelta item tag)
        (removeObservedDelta (fun candidate => candidate = tag)))
      item := by
  intro hActive
  rcases hActive with ⟨candidateTag, hAdded, hNotRemoved⟩
  change ((item = item ∧ candidateTag = tag) ∨ False) at hAdded
  rcases hAdded with hAdded | hFalse
  · apply hNotRemoved
    change False ∨ candidateTag = tag
    exact Or.inr hAdded.2
  · exact False.elim hFalse

/-- Tombstoning every add-tag for an item makes the item inactive. -/
theorem inactive_when_all_tags_removed
    (s : AuthState Item Tag) (item : Item)
    (hAllRemoved : ∀ tag, s.added item tag → s.removed tag) :
    ¬ active s item := by
  intro hActive
  rcases hActive with ⟨tag, hAdded, hNotRemoved⟩
  exact hNotRemoved (hAllRemoved tag hAdded)

end AuthState

/-- A role assignment is a member-capability pair. -/
abbrev CapabilityAssignment (Member Capability : Type) := Member × Capability

/--
Normalized authorization state. Membership and per-member capabilities are
independent observed-remove sets and therefore share one causal normalization
policy without conflating their tag namespaces.
-/
structure AuthorizationState
    (Member Capability MemberTag CapabilityTag : Type) where
  members : AuthState Member MemberTag
  capabilities : AuthState (CapabilityAssignment Member Capability) CapabilityTag

namespace AuthorizationState

variable {Member Capability MemberTag CapabilityTag : Type}

/-- Empty membership and capability state. -/
def empty : AuthorizationState Member Capability MemberTag CapabilityTag where
  members := AuthState.empty
  capabilities := AuthState.empty

/-- Componentwise join of immutable membership and capability facts. -/
def join
    (a b : AuthorizationState Member Capability MemberTag CapabilityTag) :
    AuthorizationState Member Capability MemberTag CapabilityTag where
  members := AuthState.join a.members b.members
  capabilities := AuthState.join a.capabilities b.capabilities

/-- Extensional equality for normalized authorization state. -/
theorem ext
    {a b : AuthorizationState Member Capability MemberTag CapabilityTag}
    (hMembers : a.members = b.members)
    (hCapabilities : a.capabilities = b.capabilities) : a = b := by
  cases a with
  | mk am ac =>
      cases b with
      | mk bm bc =>
          cases hMembers
          cases hCapabilities
          rfl

theorem join_comm
    (a b : AuthorizationState Member Capability MemberTag CapabilityTag) :
    join a b = join b a := by
  apply ext
  · exact AuthState.join_comm a.members b.members
  · exact AuthState.join_comm a.capabilities b.capabilities

theorem join_assoc
    (a b c : AuthorizationState Member Capability MemberTag CapabilityTag) :
    join (join a b) c = join a (join b c) := by
  apply ext
  · exact AuthState.join_assoc a.members b.members c.members
  · exact AuthState.join_assoc a.capabilities b.capabilities c.capabilities

theorem join_idem
    (a : AuthorizationState Member Capability MemberTag CapabilityTag) :
    join a a = a := by
  apply ext
  · exact AuthState.join_idem a.members
  · exact AuthState.join_idem a.capabilities

/-- Membership in the normalized authorization state. -/
def memberActive
    (s : AuthorizationState Member Capability MemberTag CapabilityTag)
    (member : Member) : Prop :=
  AuthState.active s.members member

/-- A member currently holds a capability iff one grant-tag remains live. -/
def capabilityActive
    (s : AuthorizationState Member Capability MemberTag CapabilityTag)
    (member : Member) (capability : Capability) : Prop :=
  AuthState.active s.capabilities (member, capability)

/-- First-class membership-grant delta. -/
def memberGrantDelta (member : Member) (tag : MemberTag) :
    AuthorizationState Member Capability MemberTag CapabilityTag where
  members := AuthState.addDelta member tag
  capabilities := AuthState.empty

/-- First-class observed membership-revocation delta. -/
def memberRevokeObservedDelta (observed : MemberTag → Prop) :
    AuthorizationState Member Capability MemberTag CapabilityTag where
  members := AuthState.removeObservedDelta observed
  capabilities := AuthState.empty

/-- First-class role/capability grant delta. -/
def capabilityGrantDelta
    (member : Member) (capability : Capability) (tag : CapabilityTag) :
    AuthorizationState Member Capability MemberTag CapabilityTag where
  members := AuthState.empty
  capabilities := AuthState.addDelta (member, capability) tag

/-- First-class observed role/capability revocation delta. -/
def capabilityRevokeObservedDelta (observed : CapabilityTag → Prop) :
    AuthorizationState Member Capability MemberTag CapabilityTag where
  members := AuthState.empty
  capabilities := AuthState.removeObservedDelta observed

/-- Apply one already-validated authorization delta. -/
def applyDelta
    (s d : AuthorizationState Member Capability MemberTag CapabilityTag) :
    AuthorizationState Member Capability MemberTag CapabilityTag :=
  join s d

/-- Apply validated authorization deltas in an arbitrary replay order. -/
def applyAll :
    AuthorizationState Member Capability MemberTag CapabilityTag →
    List (AuthorizationState Member Capability MemberTag CapabilityTag) →
    AuthorizationState Member Capability MemberTag CapabilityTag
  | s, [] => s
  | s, d :: ds => applyAll (applyDelta s d) ds

/-- Adjacent validated membership or role deltas commute. -/
theorem applyAll_swap
    (s a b : AuthorizationState Member Capability MemberTag CapabilityTag)
    (rest : List (AuthorizationState Member Capability MemberTag CapabilityTag)) :
    applyAll s (a :: b :: rest) = applyAll s (b :: a :: rest) := by
  have h : join (join s a) b = join (join s b) a := by
    rw [join_assoc, join_assoc]
    rw [join_comm a b]
  exact congrArg (fun state => applyAll state rest) h

/--
Membership-and-role confluence: every permutation of the same validated deltas
produces the same normalized member and per-member capability state.
-/
theorem applyAll_perm
    {xs ys :
      List (AuthorizationState Member Capability MemberTag CapabilityTag)}
    (h : xs.Perm ys)
    (s : AuthorizationState Member Capability MemberTag CapabilityTag) :
    applyAll s xs = applyAll s ys := by
  induction h generalizing s with
  | nil => rfl
  | cons x h ih =>
      exact ih (applyDelta s x)
  | swap x y rest =>
      exact applyAll_swap s y x rest
  | trans h₁ h₂ ih₁ ih₂ =>
      exact (ih₁ s).trans (ih₂ s)

/-- A fresh concurrent role grant survives a revocation that did not observe it. -/
theorem fresh_capability_grant_survives_unseen_revoke
    (member : Member) (capability : Capability)
    (oldTag newTag : CapabilityTag) (hFresh : newTag ≠ oldTag) :
    capabilityActive
      (join
        (capabilityGrantDelta (MemberTag := MemberTag)
          member capability newTag)
        (capabilityRevokeObservedDelta (MemberTag := MemberTag)
          (fun tag => tag = oldTag)))
      member capability := by
  simpa [capabilityActive, join, capabilityGrantDelta,
    capabilityRevokeObservedDelta] using
    (AuthState.fresh_add_survives_observed_remove
      (member, capability) oldTag newTag hFresh)

/-- A role revocation tombstones each role-grant tag visible in its causal context. -/
theorem observed_capability_tag_is_tombstoned
    (member : Member) (capability : Capability) (tag : CapabilityTag) :
    (join
      (capabilityGrantDelta (MemberTag := MemberTag)
        member capability tag)
      (capabilityRevokeObservedDelta (MemberTag := MemberTag)
        (fun candidate => candidate = tag))).capabilities.removed tag := by
  exact Or.inr rfl

/-- A visible revocation blocks the sole capability tag in a later causal view. -/
theorem observed_only_capability_grant_is_inactive
    (member : Member) (capability : Capability) (tag : CapabilityTag) :
    ¬ capabilityActive
      (join
        (capabilityGrantDelta (MemberTag := MemberTag)
          member capability tag)
        (capabilityRevokeObservedDelta (MemberTag := MemberTag)
          (fun candidate => candidate = tag)))
      member capability := by
  simpa [capabilityActive, join, capabilityGrantDelta,
    capabilityRevokeObservedDelta] using
    (AuthState.observed_only_tag_is_inactive (member, capability) tag)

end AuthorizationState

end CausalDagCgka
