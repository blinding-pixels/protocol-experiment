"""Finite executable oracle for observed-remove membership/capability lifecycle.

This is deliberately not cryptography.  It checks the lifecycle assumptions
that sit underneath the existing authorization-confluence theorem.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import FrozenSet, Iterable

Member = str
Capability = str
Tag = str
CapabilityFact = tuple[Member, Capability, Tag]
MembershipFact = tuple[Member, Tag]


@dataclass(frozen=True)
class AuthorizationState:
    memberships: FrozenSet[MembershipFact] = field(default_factory=frozenset)
    removed_membership_tags: FrozenSet[Tag] = field(default_factory=frozenset)
    capabilities: FrozenSet[CapabilityFact] = field(default_factory=frozenset)
    removed_capability_tags: FrozenSet[Tag] = field(default_factory=frozenset)

    def join(self, other: "AuthorizationState") -> "AuthorizationState":
        return AuthorizationState(
            memberships=self.memberships | other.memberships,
            removed_membership_tags=(
                self.removed_membership_tags | other.removed_membership_tags
            ),
            capabilities=self.capabilities | other.capabilities,
            removed_capability_tags=(
                self.removed_capability_tags | other.removed_capability_tags
            ),
        )

    def active_membership_tags(self, member: Member) -> FrozenSet[Tag]:
        return frozenset(
            tag
            for candidate, tag in self.memberships
            if candidate == member and tag not in self.removed_membership_tags
        )

    def active_capability_tags(
        self, member: Member, capability: Capability
    ) -> FrozenSet[Tag]:
        return frozenset(
            tag
            for candidate, granted_capability, tag in self.capabilities
            if candidate == member
            and granted_capability == capability
            and tag not in self.removed_capability_tags
        )

    def member_active(self, member: Member) -> bool:
        return bool(self.active_membership_tags(member))

    def capability_active(self, member: Member, capability: Capability) -> bool:
        return bool(self.active_capability_tags(member, capability))

    def operation_authorized(self, member: Member, capability: Capability) -> bool:
        return self.member_active(member) and self.capability_active(
            member, capability
        )


def member_grant(member: Member, tag: Tag) -> AuthorizationState:
    return AuthorizationState(memberships=frozenset({(member, tag)}))


def capability_grant(
    context: AuthorizationState,
    member: Member,
    capability: Capability,
    tag: Tag,
) -> AuthorizationState:
    """Create a grant delta only when the target is active in signed context."""

    if not context.member_active(member):
        raise ValueError("capability target is not active in the signed causal context")
    return AuthorizationState(capabilities=frozenset({(member, capability, tag)}))


def member_revoke_observed(tags: Iterable[Tag]) -> AuthorizationState:
    return AuthorizationState(removed_membership_tags=frozenset(tags))


def capability_revoke_observed(tags: Iterable[Tag]) -> AuthorizationState:
    return AuthorizationState(removed_capability_tags=frozenset(tags))


def removal_only_rejoin_state(
    *,
    member: Member = "alice",
    capability: Capability = "admin",
    old_member_tag: Tag = "m1",
    new_member_tag: Tag = "m2",
    capability_tag: Tag = "c1",
) -> AuthorizationState:
    initial_member = member_grant(member, old_member_tag)
    initial = initial_member.join(
        capability_grant(initial_member, member, capability, capability_tag)
    )
    removed = initial.join(member_revoke_observed({old_member_tag}))
    return removed.join(member_grant(member, new_member_tag))


def coupled_removal_rejoin_state(
    *,
    member: Member = "alice",
    capability: Capability = "admin",
    old_member_tag: Tag = "m1",
    new_member_tag: Tag = "m2",
    capability_tag: Tag = "c1",
) -> AuthorizationState:
    initial_member = member_grant(member, old_member_tag)
    initial = initial_member.join(
        capability_grant(initial_member, member, capability, capability_tag)
    )
    removed = initial.join(member_revoke_observed({old_member_tag})).join(
        capability_revoke_observed({capability_tag})
    )
    return removed.join(member_grant(member, new_member_tag))


def fresh_incarnation_rejoin_state(
    *,
    old_member: Member = "alice#1",
    new_member: Member = "alice#2",
    capability: Capability = "admin",
    old_member_tag: Tag = "m1",
    new_member_tag: Tag = "m2",
    capability_tag: Tag = "c1",
) -> AuthorizationState:
    if old_member == new_member:
        raise ValueError("fresh incarnation must have a distinct member identity")
    initial_member = member_grant(old_member, old_member_tag)
    initial = initial_member.join(
        capability_grant(initial_member, old_member, capability, capability_tag)
    )
    removed = initial.join(member_revoke_observed({old_member_tag}))
    return removed.join(member_grant(new_member, new_member_tag))
