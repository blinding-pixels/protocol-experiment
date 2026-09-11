# Current correction

The imported contract is corrected as described in
`formal/documents/EASYCRYPT_IMPORTED_CONTRACT_REPAIR.md`. The reproducer now
rejects its forbidden actor, and the driver also checks legitimate and illegal
interface admissions. This does not certify the complete supporting closure.

The historical diagnostic description below records the original finding.

# Quarantined imported-boundary diagnostics

These theories are **not production proof dependencies**. Never import
`BeeKemBoundaryContradiction.ec` into the live-key proof. At the historical checkpoint,
it proved `false` using the then-unrestricted imported BeeKEM axiom. That is a critical
failure of the imported statement, not successful security verification.

`BeeKemBoundaryCounterexample.ec` imports no local security axiom. It uses the
actual `BeeKemKiGame` and aliases of existing concrete witness procedures. An
implementation accepted by `BEEKEM_KI_ADVERSARY` reads the real challenger's
`hidden_bit` directly, makes no oracle queries, and wins with probability one.
The declared module type does not prohibit that access. Both empty-user and
initialized-member executions are checked. A constant-guess control wins with
probability one half.

`BeeKemBoundaryNoAxiomSanity.ec` deliberately attempts `false` without importing
the disputed boundary. It must fail at its strict proof goal. This is a sanity
check, not a general consistency proof.

`BeeKemBoundaryContradiction.ec` then imports exactly the existing boundary and
instantiates it with a nonempty user list, kappa = 1, c = 0, n = 2, h = 1. All
of its explicit correctness, safety, counter, and logarithm premises are proved
before the imported theorem is applied. The resulting inequality is
one half <= zero, independently of the existential primitive adversaries.

Run from the repository root, after making the pinned image available:

```sh
python3 tools/easycrypt/check_imported_boundary.py --evidence /tmp/unique-boundary-evidence
```

The checker is the immutable Docker image already used by the project. An
optional `--chroot PATH` runs the same checker from a separately verified export
of that image, under its original charlie user. The tool does not install or
alter a checker, library, solver, or cryptographic assumption.

The driver independently compiles the counterexample's entire local dependency
closure in a new directory containing only the needed sources. It verifies that
the only additional local axiom is the unchanged
`beekem_theorem1_imported_normalized`, checks the boundary-free negative control,
and then tests the contradiction. Every command, exit, source hash and generated
`.eco` hash is recorded. Timeouts and malformed diagnostics fail closed.

**Historical safety outcome before the correction: exit 1,
`INCONSISTENT_IMPORTED_BOUNDARY`.** An accepted `false` theorem must never be
reported as a green security check. A semantic rejection of this particular
reproducer is only a regression-test success; it does not prove the absence of
other inconsistencies or satisfy the full live-key acceptance criteria.

See `formal/documents/EASYCRYPT_IMPORTED_BOUNDARY_INCONSISTENCY.md` for the exact
scope, implications, and distinction from a cryptanalytic attack on BeeKEM.

The corrected contract now has expected driver exit zero and status
`REPRODUCER_REJECTED`, with both legitimate admission controls accepted and
all five private-state bypass controls rejected. The unsafe fixture experiment
remains reproducible without importing its formerly overbroad security claim.
