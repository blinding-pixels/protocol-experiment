import CausalDagCgka.Authorization
import CausalDagCgka.Logic

namespace CausalDagCgka

/--
A capability-gated operation whose author, required capability, causal context,
and operation identifier are covered by a transcript digest and signature.
Cryptographic signature soundness is an assumption to the Lean model, not a
computational theorem proved here.
-/
structure CapabilityOperation
    (Member Capability OperationId ContextId Digest Signature : Type) where
  operationId : OperationId
  author : Member
  requiredCapability : Capability
  causalContext : ContextId
  digest : Digest
  signature : Signature

namespace CapabilityOperation

variable
  {Member Capability MemberTag CapabilityTag OperationId ContextId Digest Signature : Type}

/-- The signed digest commits to the complete capability-gated operation header. -/
def transcriptBound
    (bind : OperationId → Member → Capability → ContextId → Digest)
    (operation :
      CapabilityOperation Member Capability OperationId ContextId Digest Signature) : Prop :=
  operation.digest =
    bind operation.operationId operation.author operation.requiredCapability
      operation.causalContext

/-- Signature verification under the key bound to the claimed author. -/
def signatureAccepted
    (verify : Member → Digest → Signature → Prop)
    (operation :
      CapabilityOperation Member Capability OperationId ContextId Digest Signature) : Prop :=
  verify operation.author operation.digest operation.signature

/--
Causal-context validity. Authorization is evaluated in the author's signed
causal view, never recomputed against a later merged view.
-/
def validInContext
    (contextState :
      AuthorizationState Member Capability MemberTag CapabilityTag)
    (bind : OperationId → Member → Capability → ContextId → Digest)
    (verify : Member → Digest → Signature → Prop)
    (operation :
      CapabilityOperation Member Capability OperationId ContextId Digest Signature) : Prop :=
  AuthorizationState.memberActive contextState operation.author ∧
  AuthorizationState.capabilityActive contextState operation.author
    operation.requiredCapability ∧
  transcriptBound bind operation ∧
  signatureAccepted verify operation

/-- Evidence that one signed operation is attributable to a particular member. -/
def attributableTo
    (bind : OperationId → Member → Capability → ContextId → Digest)
    (verify : Member → Digest → Signature → Prop)
    (operation :
      CapabilityOperation Member Capability OperationId ContextId Digest Signature)
    (member : Member) : Prop :=
  transcriptBound bind operation ∧
  verify member operation.digest operation.signature

/--
Abstract key-binding assumption: one accepted signature and digest cannot verify
under two different member identities. EUF-CMA and credential binding discharge
this premise in the computational layer.
-/
def UniqueSignatureBinding
    (verify : Member → Digest → Signature → Prop) : Prop :=
  ∀ ⦃first second : Member⦄ ⦃digest : Digest⦄ ⦃signature : Signature⦄,
    verify first digest signature →
    verify second digest signature →
    first = second

/-- Every causally valid capability operation carries attribution evidence. -/
theorem valid_operation_attributable
    (contextState :
      AuthorizationState Member Capability MemberTag CapabilityTag)
    (bind : OperationId → Member → Capability → ContextId → Digest)
    (verify : Member → Digest → Signature → Prop)
    (operation :
      CapabilityOperation Member Capability OperationId ContextId Digest Signature)
    (hValid : validInContext contextState bind verify operation) :
    attributableTo bind verify operation operation.author := by
  exact ⟨hValid.2.2.1, hValid.2.2.2⟩

/-- Under unique signature binding, the attributable author is unique. -/
theorem valid_operation_unique_author
    (contextState :
      AuthorizationState Member Capability MemberTag CapabilityTag)
    (bind : OperationId → Member → Capability → ContextId → Digest)
    (verify : Member → Digest → Signature → Prop)
    (operation :
      CapabilityOperation Member Capability OperationId ContextId Digest Signature)
    (hUnique : UniqueSignatureBinding verify)
    (hValid : validInContext contextState bind verify operation)
    (other : Member)
    (hOther : verify other operation.digest operation.signature) :
    other = operation.author := by
  exact hUnique hOther hValid.2.2.2

/-- Any valid capability-gated operation witnesses active membership. -/
theorem validity_requires_membership
    (contextState :
      AuthorizationState Member Capability MemberTag CapabilityTag)
    (bind : OperationId → Member → Capability → ContextId → Digest)
    (verify : Member → Digest → Signature → Prop)
    (operation :
      CapabilityOperation Member Capability OperationId ContextId Digest Signature)
    (hValid : validInContext contextState bind verify operation) :
    AuthorizationState.memberActive contextState operation.author :=
  hValid.1

/-- Any valid capability-gated operation witnesses the required capability. -/
theorem validity_requires_capability
    (contextState :
      AuthorizationState Member Capability MemberTag CapabilityTag)
    (bind : OperationId → Member → Capability → ContextId → Digest)
    (verify : Member → Digest → Signature → Prop)
    (operation :
      CapabilityOperation Member Capability OperationId ContextId Digest Signature)
    (hValid : validInContext contextState bind verify operation) :
    AuthorizationState.capabilityActive contextState operation.author
      operation.requiredCapability :=
  hValid.2.1

end CapabilityOperation

/--
Authorization plus an immutable audit ledger of accepted capability-gated
operations. Revocation can constrain later operations without deleting evidence
of a previously accepted signed operation.
-/
structure AccountableState
    (Member Capability MemberTag CapabilityTag Operation : Type) where
  authorization : AuthorizationState Member Capability MemberTag CapabilityTag
  accepted : Operation → Prop

namespace AccountableState

variable {Member Capability MemberTag CapabilityTag Operation : Type}

/-- Empty authorization and audit state. -/
def empty : AccountableState Member Capability MemberTag CapabilityTag Operation where
  authorization := AuthorizationState.empty
  accepted := fun _ => False

/-- Componentwise union of normalized authorization and immutable audit facts. -/
def join
    (a b : AccountableState Member Capability MemberTag CapabilityTag Operation) :
    AccountableState Member Capability MemberTag CapabilityTag Operation where
  authorization := AuthorizationState.join a.authorization b.authorization
  accepted := predUnion a.accepted b.accepted

/-- Extensional equality for accountable state. -/
theorem ext
    {a b : AccountableState Member Capability MemberTag CapabilityTag Operation}
    (hAuthorization : a.authorization = b.authorization)
    (hAccepted : a.accepted = b.accepted) : a = b := by
  cases a with
  | mk aa ao =>
      cases b with
      | mk ba bo =>
          cases hAuthorization
          cases hAccepted
          rfl

theorem join_comm
    (a b : AccountableState Member Capability MemberTag CapabilityTag Operation) :
    join a b = join b a := by
  apply ext
  · exact AuthorizationState.join_comm a.authorization b.authorization
  · exact predUnion_comm a.accepted b.accepted

theorem join_assoc
    (a b c : AccountableState Member Capability MemberTag CapabilityTag Operation) :
    join (join a b) c = join a (join b c) := by
  apply ext
  · exact AuthorizationState.join_assoc
      a.authorization b.authorization c.authorization
  · exact predUnion_assoc a.accepted b.accepted c.accepted

theorem join_idem
    (a : AccountableState Member Capability MemberTag CapabilityTag Operation) :
    join a a = a := by
  apply ext
  · exact AuthorizationState.join_idem a.authorization
  · exact predUnion_idem a.accepted

/-- Immutable audit delta for one already-validated signed operation. -/
def operationDelta (operation : Operation) :
    AccountableState Member Capability MemberTag CapabilityTag Operation where
  authorization := AuthorizationState.empty
  accepted := fun candidate => candidate = operation

/-- A concurrent observed role-revocation delta with no audit deletion. -/
def capabilityRevokeDelta (observed : CapabilityTag → Prop) :
    AccountableState Member Capability MemberTag CapabilityTag Operation where
  authorization := AuthorizationState.capabilityRevokeObservedDelta observed
  accepted := fun _ => False

/--
Response delta used after detecting a malicious authorized operation. Full
removal requires the responder to tombstone every visible membership and role
grant tag for the author.
-/
def evictionDelta
    (observedMemberTags : MemberTag → Prop)
    (observedCapabilityTags : CapabilityTag → Prop) :
    AccountableState Member Capability MemberTag CapabilityTag Operation where
  authorization :=
    { members := AuthState.removeObservedDelta observedMemberTags
      capabilities := AuthState.removeObservedDelta observedCapabilityTags }
  accepted := fun _ => False

/-- Apply one validated accountable delta. -/
def applyDelta
    (s d : AccountableState Member Capability MemberTag CapabilityTag Operation) :
    AccountableState Member Capability MemberTag CapabilityTag Operation :=
  join s d

/-- Apply accountable deltas in any replay order. -/
def applyAll :
    AccountableState Member Capability MemberTag CapabilityTag Operation →
    List (AccountableState Member Capability MemberTag CapabilityTag Operation) →
    AccountableState Member Capability MemberTag CapabilityTag Operation
  | s, [] => s
  | s, d :: ds => applyAll (applyDelta s d) ds

/-- Adjacent accountable deltas commute. -/
theorem applyAll_swap
    (s a b : AccountableState Member Capability MemberTag CapabilityTag Operation)
    (rest :
      List (AccountableState Member Capability MemberTag CapabilityTag Operation)) :
    applyAll s (a :: b :: rest) = applyAll s (b :: a :: rest) := by
  have h : join (join s a) b = join (join s b) a := by
    rw [join_assoc, join_assoc]
    rw [join_comm a b]
  exact congrArg (fun state => applyAll state rest) h

/-- The combined authorization-and-audit state is permutation-confluent. -/
theorem applyAll_perm
    {xs ys :
      List (AccountableState Member Capability MemberTag CapabilityTag Operation)}
    (h : xs.Perm ys)
    (s : AccountableState Member Capability MemberTag CapabilityTag Operation) :
    applyAll s xs = applyAll s ys := by
  induction h generalizing s with
  | nil => rfl
  | cons x h ih =>
      exact ih (applyDelta s x)
  | swap x y rest =>
      exact applyAll_swap s y x rest
  | trans h₁ h₂ ih₁ ih₂ =>
      exact (ih₁ s).trans (ih₂ s)

/--
Chosen role-conflict policy: concurrent-exercise-wins for an operation already
valid in its author's causal context. An unseen concurrent revocation joins the
authorization state but cannot erase or retroactively invalidate the accepted
signed operation fact.
-/
theorem valid_operation_survives_concurrent_revoke
    {OperationId ContextId Digest Signature : Type}
    (authorContext :
      AuthorizationState Member Capability MemberTag CapabilityTag)
    (bind : OperationId → Member → Capability → ContextId → Digest)
    (verify : Member → Digest → Signature → Prop)
    (operation :
      CapabilityOperation Member Capability OperationId ContextId Digest Signature)
    (hValid : CapabilityOperation.validInContext
      authorContext bind verify operation)
    (observed : CapabilityTag → Prop) :
    CapabilityOperation.validInContext authorContext bind verify operation ∧
    (join
      (operationDelta
        (Member := Member)
        (Capability := Capability)
        (MemberTag := MemberTag)
        (CapabilityTag := CapabilityTag)
        operation)
      (capabilityRevokeDelta
        (Member := Member)
        (Capability := Capability)
        (MemberTag := MemberTag)
        (CapabilityTag := CapabilityTag)
        (Operation := CapabilityOperation
          Member Capability OperationId ContextId Digest Signature)
        observed)).accepted operation := by
  refine ⟨hValid, ?_⟩
  exact Or.inl rfl

/--
By contrast, a causally later operation is blocked when its view contains the
revocation of its sole capability tag.
-/
theorem visible_revoke_blocks_later_operation
    {OperationId ContextId Digest Signature : Type}
    (member : Member) (capability : Capability) (tag : CapabilityTag)
    (bind : OperationId → Member → Capability → ContextId → Digest)
    (verify : Member → Digest → Signature → Prop)
    (operation :
      CapabilityOperation Member Capability OperationId ContextId Digest Signature)
    (hAuthor : operation.author = member)
    (hCapability : operation.requiredCapability = capability) :
    ¬ CapabilityOperation.validInContext
      (AuthorizationState.join
        (AuthorizationState.capabilityGrantDelta
          (MemberTag := MemberTag)
          member capability tag)
        (AuthorizationState.capabilityRevokeObservedDelta
          (Member := Member)
          (Capability := Capability)
          (MemberTag := MemberTag)
          (CapabilityTag := CapabilityTag)
          (fun candidate => candidate = tag)))
      bind verify operation := by
  intro hValid
  have hActive := hValid.2.1
  rw [hAuthor, hCapability] at hActive
  exact AuthorizationState.observed_only_capability_grant_is_inactive
    (MemberTag := MemberTag) member capability tag hActive

/--
Detection-and-eviction preserves the signed evidence while tombstoning the
observed membership and role tags that empowered the attributed author.
-/
theorem detection_and_eviction_preserves_evidence
    {OperationId ContextId Digest Signature : Type}
    (authorContext :
      AuthorizationState Member Capability MemberTag CapabilityTag)
    (bind : OperationId → Member → Capability → ContextId → Digest)
    (verify : Member → Digest → Signature → Prop)
    (operation :
      CapabilityOperation Member Capability OperationId ContextId Digest Signature)
    (hValid : CapabilityOperation.validInContext
      authorContext bind verify operation)
    (memberTag : MemberTag) (capabilityTag : CapabilityTag) :
    let merged :
      AccountableState
        Member Capability MemberTag CapabilityTag
        (CapabilityOperation
          Member Capability OperationId ContextId Digest Signature) :=
      join
        (operationDelta
          (Member := Member)
          (Capability := Capability)
          (MemberTag := MemberTag)
          (CapabilityTag := CapabilityTag)
          operation)
        (evictionDelta
          (Member := Member)
          (Capability := Capability)
          (MemberTag := MemberTag)
          (CapabilityTag := CapabilityTag)
          (Operation := CapabilityOperation
            Member Capability OperationId ContextId Digest Signature)
          (fun candidate => candidate = memberTag)
          (fun candidate => candidate = capabilityTag))
    CapabilityOperation.attributableTo bind verify operation operation.author ∧
    merged.accepted operation ∧
    merged.authorization.members.removed memberTag ∧
    merged.authorization.capabilities.removed capabilityTag := by
  dsimp
  refine ⟨CapabilityOperation.valid_operation_attributable
    authorContext bind verify operation hValid, ?_, ?_, ?_⟩
  · exact Or.inl rfl
  · exact Or.inr rfl
  · exact Or.inr rfl

end AccountableState

end CausalDagCgka
