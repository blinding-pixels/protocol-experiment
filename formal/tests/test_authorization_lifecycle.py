from __future__ import annotations

import unittest

from formal.authorization_lifecycle import (
    AuthorizationState,
    capability_grant,
    coupled_removal_rejoin_state,
    fresh_incarnation_rejoin_state,
    member_grant,
    member_revoke_observed,
    removal_only_rejoin_state,
)


class AuthorizationLifecycleTests(unittest.TestCase):
    def test_removal_only_then_same_identity_rejoin_revives_old_capability(self) -> None:
        state = removal_only_rejoin_state()
        self.assertTrue(state.operation_authorized("alice", "admin"))

    def test_coupled_removal_prevents_same_identity_revival(self) -> None:
        state = coupled_removal_rejoin_state()
        self.assertTrue(state.member_active("alice"))
        self.assertFalse(state.capability_active("alice", "admin"))
        self.assertFalse(state.operation_authorized("alice", "admin"))

    def test_fresh_incarnation_must_change_identity(self) -> None:
        with self.assertRaises(ValueError):
            fresh_incarnation_rejoin_state(old_member="alice", new_member="alice")
        state = fresh_incarnation_rejoin_state()
        self.assertFalse(state.capability_active("alice#2", "admin"))

    def test_dormant_capability_grant_is_rejected(self) -> None:
        with self.assertRaises(ValueError):
            capability_grant(AuthorizationState(), "alice", "admin", "c1")

    def test_partial_coupled_removal_is_rejected(self) -> None:
        initial_member = member_grant("alice", "m1")
        state = initial_member.join(
            capability_grant(initial_member, "alice", "admin", "c1")
        )
        state = state.join(member_revoke_observed({"m1"}))
        state = state.join(member_grant("alice", "m2"))
        self.assertTrue(state.operation_authorized("alice", "admin"))

    def test_plain_member_remove_does_not_touch_other_member(self) -> None:
        alice = member_grant("alice", "a1")
        bob = member_grant("bob", "b1")
        state = alice.join(bob).join(member_revoke_observed({"a1"}))
        self.assertFalse(state.member_active("alice"))
        self.assertTrue(state.member_active("bob"))


if __name__ == "__main__":
    unittest.main()
