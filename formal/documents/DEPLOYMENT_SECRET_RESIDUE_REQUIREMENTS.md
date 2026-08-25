# Deployment secret-residue requirements

## 2026-08-25 assumption revalidation

Status: **unresolved per target unless enforced and tested**.

The abstract post-erasure theorem assumes secure erasure. A deployment may make
that assumption false through storage and operating-system behavior even when
the protocol transition is correct.

Every supported target must provide evidence for:

- encrypted swap and hibernation, or an explicit unsupported finding;
- crash-dump and diagnostic-log exclusion for keys and recovered plaintext;
- bounded plaintext buffer lifetime and zeroization at the actual allocation
  boundary;
- keychain, enclave, or file-key custody and revocation behavior;
- database journal, backup, snapshot, and restore deletion semantics;
- allocator and process-restart residue;
- hardware and compiler behavior relevant to measured leakage;
- rollback resistance for receipt and revocation evidence.

An `assumed` status is not allowed. A requirement is either enforced with a
negative control or recorded as unresolved. No target inherits another target's
result by analogy.

### Current lifecycle theorem source

The current Lean lifecycle source is authored but kernel-pending. It states the
removal-only revival counterexample and the coupled-tombstone and fresh-incarnation
repairs without adding cryptography. Until the exact Lean 4.32.2 kernel accepts
`formal/current-source/CausalDagCgka/AuthorizationLifecycle.lean` under the existing
axiom audit, these are source-level candidate theorems backed by the executable
finite oracle, not newly kernel-checked results.
