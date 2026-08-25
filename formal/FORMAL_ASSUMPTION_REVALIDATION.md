# Formal assumption revalidation

Date: 2026-08-25  
Frozen origin source: `5b5d50e6d03bc5a8691fed8449e10afb9cd9fe0f`  
Frozen origin tree: `6a18759db34f15fc6f06e80b108d1ee14da36a54`

## Verdict

The protocol's **abstract conditional spine still holds** after making the new
assumptions explicit. The new evidence requirements do not invalidate the Lean
join/confluence results, the restricted segment-cover result, the imported
finite-`kappa` BeeKEM theorem, or the stated game-hop structure.

The review does **not** validate the exact frozen implementation or production
system. Those layers remain open because exact compiled mutation execution,
cross-language vector execution, full evidence-graph population, production
lifecycle tests, target measurements, and host-residue evidence are absent.

One stronger lifecycle interpretation does not survive review: member removal
alone does not permanently revoke a surviving capability across same-identity
rejoin.

## What was checked

### Canonical context construction

The frozen Rust `protocol.rs` source at blob
`af2eb7ab204a2a2ffba0cae126cd61f6a0dccc0c` uses the same schedule as the
independent Python oracle:

- authorization domain `facets-cdg-v1/authorization-state`;
- ordered unique 32-byte member identities;
- section marker `0x01` before members;
- ordered unique `(member, capability)` entries;
- section marker `0x02` before capabilities;
- capability codes `1` and `2`;
- causal-state domain `facets-cdg-v1/causal-state`;
- big-endian 32-bit policy version;
- fixed component order: DAG, forks, grants, punctures, authorization.

Fixed widths and section markers remove concatenation ambiguity. Source-level
inspection therefore found no mismatch. A-003 remains pending because the exact
Rust vector has not been compiled and compared byte-for-byte in this temporary
remote.

### Receipt evidence

The frozen Rust `consistency.rs` blob
`2499604d3821df876e153731f597a0fd3588f4f1` and the Lean receipt model both
retain signed receipts without arrival-order rejection and derive equivocation
from same-author, same-sequence, different statement bodies. This is compatible
with the abstract accountability claim.

It does not establish delivery liveness, durable storage, rollback resistance,
or production gossip.

### Membership and capability lifecycle

The formal state is a pair of independent observed-remove sets. Operation
validity requires both `memberActive` and `capabilityActive`, but member removal
does not change capability tombstones.

Counterexample:

1. add membership tag `m1` for Alice;
2. add capability tag `c1` for Alice;
3. tombstone only `m1`;
4. add membership tag `m2` for the same Alice identity.

At step 3 Alice cannot operate because membership is inactive. At step 4 the old
`c1` tag is still active, so authority revives. The executable oracle and
negative controls are in `authorization_lifecycle.py`.

This does not break confluence. It means a no-revival theorem needs one explicit
policy premise:

- coupled visible capability-tag tombstoning on authority-revoking removal; or
- incarnation-scoped identities on rejoin.

Capability grants must target a member active in the grant's signed causal
context. Unseen concurrent grants retain the selected conflict semantics and
must not be silently resolved by replay order.

## Layered result

### Abstract layer

Still conditional:

- public-state and immutable-evidence confluence;
- exact-context operation validation;
- finite-`kappa` cross-fork live-key security under the imported theorem;
- exact bounded retrospective access for bounded segment-prefix unions;
- post-erasure security under actual secure erasure;
- receipt equivocation evidence after both views are observed.

Restricted or false:

- arbitrary DAG-region logarithmic compactness remains false;
- removal-only authority non-revival is false.

### Implementation layer

Open:

- exact frozen-source correct/mutation execution;
- independent raw-outcome derivation;
- compiled Rust/Python canonical vector equality;
- complete proof-to-source-to-binary graph;
- fresh exact-target measurements.

### Production layer

Open:

- lifecycle enforcement for removal/rejoin;
- revocation propagation;
- receipt and audit persistence;
- rollback resistance;
- retention and erasure behavior;
- target host-residue requirements.

## Completion rule

A claim changes status only when a machine-readable validator derives the change
from underlying artifacts and a negative control fails for the intended reason.
This document cannot close a claim by stating that it is closed.

## Current Lean lifecycle source

`formal/current-source/CausalDagCgka/AuthorizationLifecycle.lean` now encodes:

- operation use remains blocked while membership is inactive even when a
  capability tag survives;
- same-identity rejoin revives that surviving capability;
- coupled visible capability-tag tombstoning prevents the old tag from
  reviving; and
- a fresh incarnation identity does not inherit the old identity's capability.

The source imports only the existing authorization layer and contains no
`sorry`, `admit`, `sorryAx`, new axiom, opaque primitive, or cryptographic
construction. It is not yet promoted to kernel-checked evidence: the exact Lean
4.32.2 kernel artifact could not be retrieved in this execution environment and
CI is intentionally disabled. The executable finite model and its negative
controls remain the currently executed evidence.
