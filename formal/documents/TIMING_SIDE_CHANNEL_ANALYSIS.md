# Timing and microarchitectural assurance boundary

## 2026-08-25 assumption revalidation

Status: **open for every unmeasured exact binary and target**.

Functional public-only scheduling and zeroizing secret containers do not prove
constant-time machine code. Timing, Cachegrind, assembly, and compiler evidence
is admissible only when it binds all of:

```text
source commit and source-tree hash
binary hash before and after execution
compiler and feature profile
target triple and runner identity
raw measurement artifact hash
public measurement inputs
```

Cross-target inference is forbidden. An earlier successful artifact cannot
support the frozen source if its commit differs or it omits the compiled
attack-lab layer. A failed job with no executable steps or logs is an
infrastructure finding, not leakage evidence.

The remaining work is fresh execution of the correct and exactly
one-defense-removed variants, independent scoring from raw fields, and exact
binary/target measurement. Until then, the implementation makes no current
machine-code timing claim.

### Current lifecycle theorem source

The current Lean lifecycle source is authored but kernel-pending. It states the
removal-only revival counterexample and the coupled-tombstone and fresh-incarnation
repairs without adding cryptography. Until the exact Lean 4.32.2 kernel accepts
`formal/current-source/CausalDagCgka/AuthorizationLifecycle.lean` under the existing
axiom audit, these are source-level candidate theorems backed by the executable
finite oracle, not newly kernel-checked results.
