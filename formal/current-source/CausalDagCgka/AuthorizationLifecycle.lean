import CausalDagCgka.Authorization

namespace CausalDagCgka

namespace AuthorizationLifecycle

variable {Member Capability MemberTag CapabilityTag : Type}

/--
The public authorization predicate used by capability-gated operations.  A live
capability tag is deliberately insufficient while membership is inactive.
-/
def operationAuthorized
    (state : AuthorizationState Member Capability MemberTag CapabilityTag)
    (member : Member) (capability : Capability) : Prop :=
  AuthorizationState.memberActive state member ∧
  AuthorizationState.capabilityActive state member capability

/--
History in which membership is removed but the capability tag is not, followed
by a same-identity membership re-add.  This is the load-bearing lifecycle
counterexample; it adds no new protocol state or cryptography.
-/
def removalOnlyRejoinState
    (member : Member) (capability : Capability)
    (oldMemberTag newMemberTag : MemberTag)
    (capabilityTag : CapabilityTag) :
    AuthorizationState Member Capability MemberTag CapabilityTag :=
  AuthorizationState.join
    (AuthorizationState.join
      (AuthorizationState.join
        (AuthorizationState.memberGrantDelta member oldMemberTag)
        (AuthorizationState.capabilityGrantDelta member capability capabilityTag))
      (AuthorizationState.memberRevokeObservedDelta
        (fun tag => tag = oldMemberTag)))
    (AuthorizationState.memberGrantDelta member newMemberTag)

/--
Membership-only removal blocks operation use immediately: the capability tag may
remain live, but the operation predicate still requires active membership.
-/
theorem removal_only_blocks_while_membership_inactive
    (member : Member) (capability : Capability)
    (memberTag : MemberTag) (capabilityTag : CapabilityTag) :
    let state : AuthorizationState Member Capability MemberTag CapabilityTag :=
      AuthorizationState.join
        (AuthorizationState.join
          (AuthorizationState.memberGrantDelta member memberTag)
          (AuthorizationState.capabilityGrantDelta member capability capabilityTag))
        (AuthorizationState.memberRevokeObservedDelta
          (fun tag => tag = memberTag))
    ¬ operationAuthorized state member capability := by
  dsimp [operationAuthorized]
  intro authorized
  rcases authorized with ⟨memberActive, _⟩
  simpa [AuthorizationState.memberActive, AuthorizationState.join,
    AuthorizationState.memberGrantDelta,
    AuthorizationState.capabilityGrantDelta,
    AuthorizationState.memberRevokeObservedDelta,
    AuthState.active, AuthState.join, AuthState.addDelta,
    AuthState.removeObservedDelta, AuthState.empty] using memberActive

/--
Member removal alone does not establish permanent authority revocation.  A fresh
membership tag for the same identity revives the still-live capability tag.
-/
theorem removal_only_same_identity_rejoin_revives_capability
    (member : Member) (capability : Capability)
    (oldMemberTag newMemberTag : MemberTag)
    (capabilityTag : CapabilityTag)
    (hFresh : newMemberTag ≠ oldMemberTag) :
    operationAuthorized
      (removalOnlyRejoinState member capability oldMemberTag newMemberTag
        capabilityTag)
      member capability := by
  constructor
  · refine ⟨newMemberTag, ?_⟩
    simp [removalOnlyRejoinState, AuthorizationState.memberActive,
      AuthorizationState.join, AuthorizationState.memberGrantDelta,
      AuthorizationState.capabilityGrantDelta,
      AuthorizationState.memberRevokeObservedDelta,
      AuthState.active, AuthState.join, AuthState.addDelta,
      AuthState.removeObservedDelta, AuthState.empty, hFresh]
  · refine ⟨capabilityTag, ?_⟩
    simp [removalOnlyRejoinState, AuthorizationState.capabilityActive,
      AuthorizationState.join, AuthorizationState.memberGrantDelta,
      AuthorizationState.capabilityGrantDelta,
      AuthorizationState.memberRevokeObservedDelta,
      AuthState.active, AuthState.join, AuthState.addDelta,
      AuthState.removeObservedDelta, AuthState.empty]

/--
Same-identity no-revival policy: tombstone the capability tag visible in the
remover's signed causal context together with the observed membership tag.
A later membership re-add cannot revive that tombstoned capability tag.
-/
def coupledRemovalRejoinState
    (member : Member) (capability : Capability)
    (oldMemberTag newMemberTag : MemberTag)
    (capabilityTag : CapabilityTag) :
    AuthorizationState Member Capability MemberTag CapabilityTag :=
  AuthorizationState.join
    (AuthorizationState.join
      (AuthorizationState.join
        (AuthorizationState.join
          (AuthorizationState.memberGrantDelta member oldMemberTag)
          (AuthorizationState.capabilityGrantDelta member capability capabilityTag))
        (AuthorizationState.memberRevokeObservedDelta
          (fun tag => tag = oldMemberTag)))
      (AuthorizationState.capabilityRevokeObservedDelta
        (fun tag => tag = capabilityTag)))
    (AuthorizationState.memberGrantDelta member newMemberTag)

/-- Coupled visible-tag removal prevents the old capability from reviving. -/
theorem coupled_removal_prevents_same_identity_capability_revival
    (member : Member) (capability : Capability)
    (oldMemberTag newMemberTag : MemberTag)
    (capabilityTag : CapabilityTag) :
    ¬ AuthorizationState.capabilityActive
      (coupledRemovalRejoinState member capability oldMemberTag newMemberTag
        capabilityTag)
      member capability := by
  intro active
  simpa [coupledRemovalRejoinState, AuthorizationState.capabilityActive,
    AuthorizationState.join, AuthorizationState.memberGrantDelta,
    AuthorizationState.capabilityGrantDelta,
    AuthorizationState.memberRevokeObservedDelta,
    AuthorizationState.capabilityRevokeObservedDelta,
    AuthState.active, AuthState.join, AuthState.addDelta,
    AuthState.removeObservedDelta, AuthState.empty] using active

/--
Alternative no-revival policy: rejoin under a fresh incarnation identity.  A
capability fact for the old identity cannot authorize the distinct identity.
-/
def freshIncarnationRejoinState
    (oldMember newMember : Member) (capability : Capability)
    (oldMemberTag newMemberTag : MemberTag)
    (capabilityTag : CapabilityTag) :
    AuthorizationState Member Capability MemberTag CapabilityTag :=
  AuthorizationState.join
    (AuthorizationState.join
      (AuthorizationState.join
        (AuthorizationState.memberGrantDelta oldMember oldMemberTag)
        (AuthorizationState.capabilityGrantDelta oldMember capability capabilityTag))
      (AuthorizationState.memberRevokeObservedDelta
        (fun tag => tag = oldMemberTag)))
    (AuthorizationState.memberGrantDelta newMember newMemberTag)

/-- A fresh incarnation identity does not inherit capability tags of the old one. -/
theorem fresh_incarnation_does_not_inherit_old_capability
    (oldMember newMember : Member) (capability : Capability)
    (oldMemberTag newMemberTag : MemberTag)
    (capabilityTag : CapabilityTag)
    (hDifferent : newMember ≠ oldMember) :
    ¬ AuthorizationState.capabilityActive
      (freshIncarnationRejoinState oldMember newMember capability oldMemberTag
        newMemberTag capabilityTag)
      newMember capability := by
  intro active
  simpa [freshIncarnationRejoinState,
    AuthorizationState.capabilityActive, AuthorizationState.join,
    AuthorizationState.memberGrantDelta,
    AuthorizationState.capabilityGrantDelta,
    AuthorizationState.memberRevokeObservedDelta,
    AuthState.active, AuthState.join, AuthState.addDelta,
    AuthState.removeObservedDelta, AuthState.empty, hDifferent] using active

end AuthorizationLifecycle

end CausalDagCgka
