# Authorized causal-DAG CGKA verification package

This package carries the settled points forward rather than re-litigating them:

- invariant-PPRF puncture commutativity is a supporting lemma;
- public authenticated puncture facts form the CRDT;
- constrained secret states are never unioned;
- retrospective access means post-erasure security, not forced forgetting;
- an inefficient witness rules out a bare algebraic impossibility;
- authorization confluence precedes key agreement;
- roles extend the same authorization-confluence theorem rather than creating a
  second authorization system;
- computational secrecy and non-repudiation remain reductions, not weakened
  Lean surrogates.

## Results at a glance

### Finite-`kappa` cross-fork DCGKA

BeeKEM 2026/1434 supplies a concrete protocol and reduction for every finite
`kappa >= 1` in its key-indistinguishability model. The primitive therefore
exists at the paper level.

The proved model assumes honest protocol execution, authenticated causal
broadcast, adversarial delivery and partitions, reveal queries, and adaptive
snapshot compromise. It does not by itself establish security against an
authorized Byzantine member that arbitrarily deviates from the protocol.

See `BEEKEM_PRIMARY_SOURCE_AUDIT.md`.

### Compact retrospective capability

Arbitrary causal-DAG regions do not have logarithmic exact dyadic covers in
general. In a causal antichain every subset is a causal ideal; alternating
leaves require `Omega(N)` subtree capabilities.

The solved restricted family is:

- fork, merge, authorization, and checkpoint boundaries create immutable
  segment-local linear namespaces;
- an authorized grant touches at most `b` segments;
- its intersection with each segment is a prefix;
- a depth-`d` tree covers the grant with at most `b(d + 1)` tagged subtree
  capabilities.

Thus exact capability size is `O(b log N)` for segment capacity `N <= 2^d`.

### Roles, causal authorization, and accountability

Membership and per-member capabilities are normalized by the same authenticated
observed-remove rule:

```text
Members       = AuthState Member MemberTag
Capabilities  = AuthState (Member x Capability) CapabilityTag
```

Lean proves confluence for the complete public state:

```text
(Members, Capabilities, ValidForks, Grants, Punctures)
```

The selected role-conflict policy is **causal-context validity with
concurrent-exercise-wins**:

- a role revocation tombstones the grant tags it observed;
- a fresh unseen concurrent role-grant tag survives;
- an operation already valid in its author's signed causal view remains an
  accepted immutable fact after an unseen concurrent revocation merges;
- a causally later operation that sees its sole role tag tombstoned is rejected.

Every accepted capability-gated operation is transcript-bound and structurally
attributable to its claimed author. Under the cryptographic signature/key-binding
assumptions, the resulting audit evidence supports detection and observed-tag
eviction after the fact. Roles do not force an already-authorized role holder to
behave benignly.

See:

- `ROLE_AUTHORIZATION_EXTENSION.md` for the semantics and Lean results;
- `PROVERIF_ROLE_AUTHORIZATION.md` for the exact symbolic query matrix and
  negative controls.

## Lean modules

Using Lean 4 and only `Std`, the package checks:

- `Authorization.lean`
  - generic observed-remove join laws;
  - membership and `(member, capability)` grant/revocation deltas;
  - membership-and-role permutation confluence;
  - fresh concurrent role grant survival;
  - visible sole-tag revocation blocking;
- `Accountability.lean`
  - causal-context operation validity;
  - transcript and signature attribution evidence;
  - unique author under the abstract signature-binding premise;
  - confluence of authorization plus the immutable accepted-operation ledger;
  - concurrent-exercise-wins;
  - visible-revocation blocking for later operations;
  - evidence preservation through the eviction delta;
- `PublicState.lean`
  - componentwise join-semilattice laws;
  - full permutation confluence for
    `(Members, Capabilities, ValidForks, Grants, Punctures)`;
- `Puncture.lean`
  - commutative public puncturing;
  - monotonic loss of readability;
  - no-resurrection;
- `CausalIdeal.lean`
  - every antichain subset is an ideal;
  - an ideal's intersection with a causal-linear segment is prefix-closed;
- `RegionCover.lean`
  - exact canonical dyadic prefix covers;
  - single-prefix size bounds;
- `SegmentGrant.lean`
  - exact segment-tagged bounded-union capabilities;
  - the `b(d + 1)` bound;
- `KappaExposure.lean`
  - exposure monotonicity in retained personal secrets;
- `Exposure.lean`
  - the corrected
    `E_kappa union H_rho union Granted_Gamma` content-exposure region;
- `Separation.lean`
  - operational product-state separation of live and history transitions.

CI builds with Lean 4.32.2 and warnings as errors, runs the bundled
`leanchecker`, audits axioms, and rejects `sorry`, `admit`, and `sorryAx`.
The allowed axiom set is exactly:

```text
propext
Classical.choice
Quot.sound
```

## Independent executable verification

- `model/model_check.py`
  - exhaustive observed-remove and full public-state permutation checks;
  - all `7! = 5,040` permutations of a representative five-component public
    history;
  - the concurrent-exercise policy;
  - exact prefix-cover enumeration through depth 12;
  - the alternating-leaf linear lower-bound witness;
- `model/z3_check.py`
  - bounded SMT proofs and counterexample searches;
- `model/sympy_sat_check.py`
  - independent propositional/SAT checks;
- `model/composition_symbolic.pv`
  - Dolev-Yao live/history key-schedule separation;
- `model/secret_state_union_resurrection.pv`
  - expected-failure control showing why constrained secret states must not be
    unioned;
- `model/role_authorization_symbolic.pv`
  - exact-context role authorization;
  - signed origin and identity-key attribution;
  - audit-record origin;
  - flag/evidence/eviction response correspondence;
  - blocked later-context reuse of an old role proof;
- `model/role_authorization_bypass.pv`
  - expected attack when identity and signature are checked but the role gate is
    omitted;
- `model/role_context_binding_bypass.pv`
  - expected attack when the role credential omits the causal context and can be
    replayed after revocation.

The ProVerif models are symbolic evidence. They do not reproduce BeeKEM's
computational key-indistinguishability game, prove EUF-CMA security, or prove a
constrained-PRF reduction.

## Main result and proof boundary

`COMPOSITION_THEOREM.md` gives the corrected protocol, authorization state,
operation-validity rule, exposure region, accountability boundary, and two
explicit game-hopping reductions:

- a live application-key challenge;
- an ungranted content-key challenge.

The raw BeeKEM secret remains internal. A multi-domain PRF derives independent
live and history namespaces, and the history namespace contains the constrained
segment tree. This avoids exporting a checkable relation to the raw BeeKEM
challenge secret.

Lean proves the combinatorial premises. BeeKEM supplies its finite-`kappa`
computational theorem. ProVerif checks selected symbolic correspondences. The
remaining negligible-advantage steps reduce to:

- the exact BeeKEM theorem;
- a multi-domain PRF under constrained history leakage;
- a constrained-tree PRF/PRG;
- KEM and AEAD security;
- EUF-CMA signatures;
- authenticated identity and role credentials;
- transcript-hash collision resistance;
- secure erasure.

Mechanizing those game hops belongs in EasyCrypt, CryptoVerif, or another
probabilistic cryptographic proof framework—not in a weakened Lean proposition.

## Malicious-authorized-member boundary

Roles narrow who can perform a sensitive operation. Signatures and immutable
audit facts make accepted operations attributable under the stated
cryptographic assumptions. Neither property prevents a currently authorized
role holder from deliberately exercising valid authority harmfully.

The achieved response is:

```text
unauthorized-operation prevention
+ signed attribution
+ durable evidence
+ external/application-level detection
+ observed-tag eviction
```

It is not a general Byzantine-insider theorem. This is stated in parity with
MLS's distinction between authenticated message origin and malicious-member
behavior.

## Run locally

From this directory:

```text
lake build --wfail
python model/model_check.py
python model/z3_check.py
python model/sympy_sat_check.py
```

ProVerif commands:

```text
proverif model/composition_symbolic.pv
proverif model/secret_state_union_resurrection.pv
proverif model/role_authorization_symbolic.pv
proverif model/role_authorization_bypass.pv
proverif model/role_context_binding_bypass.pv
```

The two bypass models are expected to produce attack traces and failed
correspondence queries. The CI workflow treats those failures as successful
negative-control evidence.

## Document index

- `EASYCRYPT_COMPUTATIONAL_PROOF_HANDOFF.md`
  - exact real/ideal games, reduction obligations, assumption allowlist,
    anti-cheating audit, and mandatory anti-triviality witnesses for the
    missing computational proof;
- `BEEKEM_PRIMARY_SOURCE_AUDIT.md`
  - exact BeeKEM theorem and threat-model boundary;
- `RESEARCH_FINDINGS.md`
  - concise resolution of the cross-fork, compact-capability, and role seams;
- `COMPOSITION_THEOREM.md`
  - protocol construction and computational reduction argument;
- `ROLE_AUTHORIZATION_EXTENSION.md`
  - role normalization, conflict policy, causal validity, attribution, and
    eviction semantics;
- `PROVERIF_ROLE_AUTHORIZATION.md`
  - complete role/accountability query matrix, canaries, negative controls, and
    symbolic assurance boundary;
- `FORMAL_CLAIM_LEDGER.md`
  - claim-by-claim mapping to Lean declarations, ProVerif queries, executable
    checks, and remaining assumptions;
- `ASSURANCE_BOUNDARY.md`
  - exactly what every verification tool does and does not prove.

## 2026-08-25 assumption revalidation

The abstract protocol claims remain conditional; they are not promoted by this
migration into current-source implementation or production claims. The
revalidation matrix is `../FORMAL_CLAIM_STATUS.json`, and the complete analysis
is `../FORMAL_ASSUMPTION_REVALIDATION.md`.

The review distinguishes three layers:

- The Lean semilattice, causal-context authorization, bounded segment-cover,
  exposure, separation, and immutable-evidence results remain mathematically
  compatible with the newly explicit assumptions.
- The frozen Rust context encoding was inspected at source commit
  `5b5d50e6d03bc5a8691fed8449e10afb9cd9fe0f` and matches the independent
  Python serialization schedule, but byte-for-byte execution against the exact
  compiled source remains open.
- End-to-end production retention, erasure, revocation propagation, receipt
  persistence, rollback resistance, and target-specific leakage remain open.

A new lifecycle counterexample is now explicit: member and capability tags are
independent observed-remove sets. Removing only a member tag leaves capability
tags dormant; re-adding the same identity can make them usable again. A
no-revival policy therefore requires either coupled visible capability-tag
tombstoning or incarnation-scoped member identities. This narrows the protocol
claim without adding any cryptographic construction.

The historical CI text elsewhere in this document describes the artifact at its
recorded source commit. The current temporary branch has CI disabled and must
not treat a runnerless job or a stale successful artifact as current evidence.

### Current lifecycle theorem source

The current Lean lifecycle source is authored but kernel-pending. It states the
removal-only revival counterexample and the coupled-tombstone and fresh-incarnation
repairs without adding cryptography. Until the exact Lean 4.32.2 kernel accepts
`formal/current-source/CausalDagCgka/AuthorizationLifecycle.lean` under the existing
axiom audit, these are source-level candidate theorems backed by the executable
finite oracle, not newly kernel-checked results.
