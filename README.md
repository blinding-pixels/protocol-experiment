# Causal-DAG Assurance Prototype

Standalone continuation of the causal-DAG assurance and executable attack-lab
prototype that was previously staged under the unrelated Facets repository.

The owner-selected remote for this phase is:

```text
repository: blinding-pixels/protocol-experiment
branch: main
path: /
```

The repository is dedicated to this research artifact and carries no GitHub
Actions workflow. CI remains off until the exact-source toolchain and runner
configuration can execute without notification spam or runnerless failures.

This work is intentionally limited to assumption removal, evidence integrity,
negative controls, formal-claim correction, and reproducibility. It must not add
new cryptographic primitives, constructions, ratchets, or protocol layers.

## Provenance

- Origin repository: `blinding-pixels/Facets`
- Origin branch: `formal/causal-dag-cgka`
- Frozen pre-extraction source commit: `5b5d50e6d03bc5a8691fed8449e10afb9cd9fe0f`
- Frozen origin tree: `6a18759db34f15fc6f06e80b108d1ee14da36a54`
- Facets preservation checkpoint: `976783a330e4f5f5991b65824741bc30bb025f97`
- Origin path: `research/causal-dag-cgka/`

The Facets research workflows were archived and PR 268 was closed. No continuing
research implementation belongs in Facets.

## Formal revalidation verdict

The protocol's abstract conditional spine still holds after the new evidence
and lifecycle assumptions are made explicit. The review does not promote those
abstract results into current compiled-source or production claims.

One stronger lifecycle interpretation is false:

> Membership removal alone does not permanently revoke a surviving capability
> across same-identity rejoin.

Membership tags and capability tags are independent observed-remove facts. A
member-only tombstone makes an old capability dormant, but re-adding the same
identity can make that capability usable again. A no-revival policy therefore
requires either:

1. coupled tombstoning of every visible capability tag during an
   authority-revoking removal; or
2. incarnation-scoped identities so a rejoin receives a fresh identity.

A capability grant must also target a member active in the grant's signed causal
context. These are lifecycle rules, not new cryptography.

The complete result is in `formal/FORMAL_ASSUMPTION_REVALIDATION.md`. Exact
claim states are machine-readable in `formal/FORMAL_CLAIM_STATUS.json`. The
original historical formal source remains byte-preserved under
`formal/historical-source-7f685d35/`; updated formal documents are under
`formal/documents/`.

## Current evidence

Run:

```text
python tools/run_assurance_checks.py --output evidence/local-test-report.json
```

Current local result: 72 tests passed, including negative controls for
conjunctive dual-target identity, canonical public-state encoding, stale evidence,
production-obligation separation, target binding, lifecycle revival, formal
claim drift, and documentation overclaiming.

The test report is evidence of the local validators and executable lifecycle
model. It is not exact Rust mutation execution, a new Lean/EasyCrypt/ProVerif
kernel run, production integration, or target leakage evidence.

## Continuation order

1. Preserve this complete working state and its historical archives in the
   dedicated protocol-experiment repository.
2. Import or reconstruct the exact frozen Rust/formal source tree as live,
   hash-addressable source rather than relying only on preserved archives.
3. Build and execute every correct and exactly one-defense-removed binary, then
   derive outcomes independently from raw fields.
4. Emit the canonical public-state vector from compiled Rust and require
   byte-for-byte equality with the independent oracle.
5. Populate the complete proof-to-source-to-binary evidence graph.
6. Execute lifecycle and persistence obligations through production adapters.
7. Generate fresh timing, cache, and assembly evidence for each exact supported
   binary and target.
8. Turn every deployment-residue assumption into an enforced requirement or an
   explicit unresolved finding.

No item is complete because this README says so. Status and exact local evidence
hashes live in `ASSUMPTION_REGISTER.json`.
