# Simplified trust and consistency model

## 2026-08-25 assumption revalidation

Status: **conditional abstract result; implementation and production evidence
open**.

The protocol derives one public causal-context digest from fixed-width,
domain-separated components:

```text
policy version
DAG root/frontier digest
valid-fork digest
retrospective-grant digest
public-puncture digest
normalized member set
normalized (member, capability) set
```

The frozen Rust source uses ordered sets, fixed 32-byte identities, one-byte
capability codes, explicit section markers, big-endian policy version, and the
same domains as the independent Python oracle. This removes insertion-order and
duplicate ambiguity at the source level. Exact compiled byte equality remains
an execution obligation.

Consistency receipts are immutable signed statements of:

```text
author
per-device sequence
previous receipt digest
canonical causal-state digest
```

Receipt evidence joins by set union. Same-author, same-sequence,
different-statement pairs are durable equivocation evidence. Receipt sequence
numbers do not order the group DAG and do not create consensus. Missing parents
are analysis findings that may resolve after delayed gossip.

The simplified trust model does not solve receipt-gossip liveness, rollback of
local evidence, or deletion of evidence from production storage. Those remain
production obligations.

Membership and capability sets are independent. This is required for their
observed-remove semantics but means membership removal alone leaves dormant
capability tags. Authority non-revival requires coupled visible capability-tag
tombstoning or incarnation-scoped identities.

### Current lifecycle theorem source

The current Lean lifecycle source is authored but kernel-pending. It states the
removal-only revival counterexample and the coupled-tombstone and fresh-incarnation
repairs without adding cryptography. Until the exact Lean 4.32.2 kernel accepts
`formal/current-source/CausalDagCgka/AuthorizationLifecycle.lean` under the existing
axiom audit, these are source-level candidate theorems backed by the executable
finite oracle, not newly kernel-checked results.
