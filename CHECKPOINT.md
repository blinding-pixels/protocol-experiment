# Canonical migration checkpoint — 2026-08-25

The dedicated continuation repository is:

```text
repository: blinding-pixels/protocol-experiment
branch: main
path: /
```

The live migration was completed by remote commit
`585122ba04c19cddb3a98f98839909fa83ec573b`
(`chore: complete live protocol assurance migration`). This checkpoint updates
older migration notes that predated the final document publication commits.

No repository was archived or deleted as part of this migration. `eshaan-os` was
left untouched. The frozen Facets branch remains available as origin evidence;
no additional work should be performed there.

## Present in the canonical repository

- live assumption-reduction and evidence-integrity source;
- conjunctive dual-target identity validation and negative controls;
- canonical public-state oracle and vector;
- proof-to-source-to-binary evidence-graph validators;
- target-bound timing/cache/assembly evidence validators;
- production-integration and deployment-residue obligation registers;
- executable authorization-lifecycle model and negative controls;
- current Lean lifecycle theorem source pinned to Lean 4.32.2;
- formal assumption revalidation and machine-readable claim-status matrix;
- browsable deployment, operational-fidelity, trust/consistency, timing,
  BeeKEM, role-authorization, composition, and formal-package documents;
- exact 77-test local report with no failures or errors;
- verified twelve-part historical text snapshot and retained historical binary
  evidence;
- provenance manifests tying the continuation back to the frozen Facets source.

CI remains disabled. No GitHub Actions workflow is present in this repository.

## Current formal verdict

The abstract conditional protocol spine still holds under its explicitly stated
cryptographic, erasure, delivery, and operational assumptions.

One stronger lifecycle interpretation is false:

> Membership removal alone does not permanently revoke a surviving capability
> when the same identity is later re-added.

Membership and capability grants are independent observed-remove facts. A plain
membership tombstone can make an old capability dormant without destroying it;
a same-identity rejoin can reactivate it.

Two no-new-cryptography repairs are modeled:

1. coupled tombstoning of every visible capability tag during an
   authority-revoking removal;
2. incarnation-scoped member identities, so rejoin creates a fresh identity.

The current Lean lifecycle module formalizes the counterexample and both repairs,
but remains **kernel-pending** until the exact Lean 4.32.2 package and existing
axiom audit run on the reconstructed complete source tree.

## Explicitly still open

- reconstruct the exact frozen 84-file Rust and full formal origin tree as live,
  browsable, hash-addressable source under a non-conflicting origin namespace;
- build and execute every correct and exactly one-defense-removed compiled
  binary outside Facets;
- compare the compiled Rust canonical-state vector byte-for-byte with the
  independent oracle;
- populate the complete proof-to-source-to-binary graph with fresh exact-source
  artifacts;
- run production lifecycle and persistence fault-injection checks;
- generate fresh timing, cache, and assembly evidence for every exact supported
  binary and target;
- obtain exact Lean 4.32.2 kernel acceptance and the existing restricted axiom
  audit for the current lifecycle module.

The historical snapshot preserves the source bytes, but it is not represented as
current execution evidence. No new cryptographic primitive, construction,
ratchet, serializer, or protocol layer has been added.
