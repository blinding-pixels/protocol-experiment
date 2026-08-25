# Assumption-removal progress

## Verified in this standalone history

- Dual-target result identity is conjunctive across schema, scenario, layer,
  embedded source commit, verified source-tree hash, stable pre/post binary
  identity, distinct binary bytes, and every supplied attack/transcript digest.
- All requested dual-target negative controls pass, including equal-first /
  different-later digests and one-sided or missing identity fields.
- The independent canonical public-state oracle normalizes insertion order and
  duplicates and binds domains, policy version, component positions, member
  identities, and capability codes.
- Evidence-graph validation rejects stale hashes, loose substring symbols,
  missing exact declarations, circular or self-attested dependencies, unbound
  binaries, cross-target measurements, and verified claims without a negative
  control.
- Prototype tests and documentation cannot close production retention, erasure,
  audit persistence, revocation propagation, rollback, authorization lifecycle,
  or host-residue obligations.
- Earlier successful formal and Rust/Verus artifacts are retained with exact
  hashes, but the admissibility validator rejects them as substitutes for the
  frozen attack-lab head because their source commits and required layers do not
  match.
- The formal claim matrix and all updated formal documents are checked against
  overclaiming and missing revalidation boundaries.
- The executable authorization-lifecycle model demonstrates the same-identity
  capability-revival counterexample and verifies two valid no-revival policy
  shapes: coupled visible capability tombstoning or a fresh incarnation
  identity.
- Seventy-seven local tests pass. The stable report is
  `evidence/local-test-report.json`.

## Formal result after assumption revalidation

The abstract protocol remains conditionally coherent:

- public-state and immutable-evidence confluence;
- exact-context operation validation;
- finite-`kappa` BeeKEM composition under the imported theorem and stated
  assumptions;
- exact bounded retrospective access for bounded segment-prefix unions;
- post-erasure security only under actual secure erasure;
- receipt-equivocation evidence once both signed views are observed.

The following stronger statement is false:

- membership tombstoning alone permanently prevents an old capability from
  reviving after the same identity rejoins.

This is a lifecycle-policy correction, not a failure of confluence and not a
reason to add cryptography.

## Implemented but still open pending underlying artifacts

- The canonical Python vector still needs byte-for-byte comparison with the
  compiled exact frozen Rust implementation.
- The strict evidence graph still needs the complete frozen proof/source tree,
  build manifests, executable hashes, and fresh measurement artifacts.
- Target binding is enforced by the validator, but no fresh standalone
  timing/cache/assembly measurements exist yet.
- Production authorization removal/rejoin must implement and test one explicit
  no-revival policy.

## Open

- Record the stable protocol-experiment content commit after the final source
  import.
- Import or reconstruct the complete frozen origin tree as live source.
- Build and execute all correct and one-defense-removed Rust variants outside
  Facets.
- Re-run the current formal source with its pinned kernels and tools; retained
  historical green artifacts remain historical, not current evidence.
- Run production lifecycle integration tests for retention, erasure, audit
  persistence, revocation propagation, rollback, and authorization lifecycle.
- Resolve or enforce every target-specific deployment-residue requirement.

No item above is treated as complete merely because this file says it is.
Machine-readable status and exact evidence hashes live in
`ASSUMPTION_REGISTER.json`.

## Current Lean lifecycle source

- `formal/current-source/CausalDagCgka/AuthorizationLifecycle.lean` is authored
  against the pinned Lean 4.32.2 package source.
- It formalizes the dormant-capability boundary, same-identity revival
  counterexample, coupled-tombstone repair, and fresh-incarnation repair.
- It imports only the existing authorization layer and contains no placeholder,
  new axiom, opaque primitive, or cryptographic construction.
- Exact Lean kernel acceptance and the existing axiom audit remain open because
  the official release asset could not be retrieved in this environment and CI
  is intentionally disabled.
