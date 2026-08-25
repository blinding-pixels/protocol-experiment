# Operational fidelity

## 2026-08-25 assumption revalidation

Status: **open for production integration**.

The research package establishes conditional abstract properties and provides
prototype validators. It does not establish that a deployed application uses
the same transitions, encoding, persistence, or erasure paths.

Production evidence must independently cover:

- exact canonical context bytes at the production call site;
- capability grants only to members active in the signed causal view;
- authority-revoking removal through coupled visible capability-tag
  tombstoning, or fresh-incarnation identity enforcement;
- revocation propagation across offline devices and forks;
- durable accepted-operation and receipt evidence;
- rollback-resistant receipt sequence and predecessor state;
- finite-`kappa` retention and actual deletion behavior;
- crash, retry, partial-write, and restore fault injection;
- exact binary/source/target provenance for every measurement.

Prototype tests, documentation, and historical workflow success are not
admissible substitutes for these paths. Each production obligation remains open
until an integration test or production trace includes a load-bearing negative
control.

### Current lifecycle theorem source

The current Lean lifecycle source is authored but kernel-pending. It states the
removal-only revival counterexample and the coupled-tombstone and fresh-incarnation
repairs without adding cryptography. Until the exact Lean 4.32.2 kernel accepts
`formal/current-source/CausalDagCgka/AuthorizationLifecycle.lean` under the existing
axiom audit, these are source-level candidate theorems backed by the executable
finite oracle, not newly kernel-checked results.
