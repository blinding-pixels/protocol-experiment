"""Independent oracle for the Rust canonical public-state encoding.

This is not a new protocol or primitive. It mirrors the public serialization
schedule in the frozen Rust implementation so permutations, duplicates, domain
changes, and policy-version changes can be tested independently.
"""

from __future__ import annotations

import hashlib
from dataclasses import dataclass
from enum import IntEnum
from typing import Iterable

AUTHORIZATION_DOMAIN = b"facets-cdg-v1/authorization-state"
CAUSAL_STATE_DOMAIN = b"facets-cdg-v1/causal-state"


class Capability(IntEnum):
    MANAGE_GROUP = 1
    CREATE_FORK = 2


@dataclass(frozen=True)
class CausalStateComponents:
    dag_root: bytes
    valid_forks_digest: bytes
    grants_digest: bytes
    punctures_digest: bytes
    policy_version: int

    def __post_init__(self) -> None:
        for name in (
            "dag_root",
            "valid_forks_digest",
            "grants_digest",
            "punctures_digest",
        ):
            value = getattr(self, name)
            if not isinstance(value, bytes) or len(value) != 32:
                raise ValueError(f"{name} must be exactly 32 bytes")
        if not isinstance(self.policy_version, int) or not 0 <= self.policy_version <= 0xFFFFFFFF:
            raise ValueError("policy_version must fit an unsigned 32-bit integer")


def _identity(value: bytes, description: str) -> bytes:
    if not isinstance(value, bytes) or len(value) != 32:
        raise ValueError(f"{description} must be exactly 32 bytes")
    return value


def _authorization_digest_with_domain(
    members: Iterable[bytes],
    capabilities: Iterable[tuple[bytes, Capability]],
    domain: bytes,
) -> bytes:
    normalized_members = sorted({_identity(member, "member") for member in members})
    normalized_capabilities = sorted(
        {
            (_identity(member, "capability member"), Capability(capability))
            for member, capability in capabilities
        },
        key=lambda item: (item[0], int(item[1])),
    )
    hasher = hashlib.sha256()
    hasher.update(domain)
    hasher.update(b"\x01")
    for member in normalized_members:
        hasher.update(member)
    hasher.update(b"\x02")
    for member, capability in normalized_capabilities:
        hasher.update(member)
        hasher.update(bytes((int(capability),)))
    return hasher.digest()


def authorization_digest(
    members: Iterable[bytes],
    capabilities: Iterable[tuple[bytes, Capability]],
) -> bytes:
    return _authorization_digest_with_domain(
        members, capabilities, AUTHORIZATION_DOMAIN
    )


def _context_id_with_domains(
    state: CausalStateComponents,
    members: Iterable[bytes],
    capabilities: Iterable[tuple[bytes, Capability]],
    *,
    authorization_domain: bytes,
    causal_state_domain: bytes,
) -> bytes:
    authorization = _authorization_digest_with_domain(
        members, capabilities, authorization_domain
    )
    hasher = hashlib.sha256()
    hasher.update(causal_state_domain)
    hasher.update(state.policy_version.to_bytes(4, "big"))
    hasher.update(state.dag_root)
    hasher.update(state.valid_forks_digest)
    hasher.update(state.grants_digest)
    hasher.update(state.punctures_digest)
    hasher.update(authorization)
    return hasher.digest()


def context_id(
    state: CausalStateComponents,
    members: Iterable[bytes],
    capabilities: Iterable[tuple[bytes, Capability]],
) -> bytes:
    return _context_id_with_domains(
        state,
        members,
        capabilities,
        authorization_domain=AUTHORIZATION_DOMAIN,
        causal_state_domain=CAUSAL_STATE_DOMAIN,
    )
