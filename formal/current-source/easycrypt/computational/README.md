# Computational proof development

Status: **Deliverable A's unauthorized-operation reduction and the BeeKEM KI-DCGKA foundation are checker-accepted. Application Deliverables L and C remain open.**

This directory is the computational development required by
`formal/documents/EASYCRYPT_COMPUTATIONAL_PROOF_HANDOFF.md`. The historical
EasyCrypt files remain historical evidence and are not imported into this
proof closure.

## Public Deliverable A theorem

`ComputationalProof.ec` imports the active A0--A5 dependency closure and prints
`UnauthorizedOriginFinalBound.adv_unauthorized_origin_bound`:

```text
Pr[UnauthorizedOriginPartitionGame(A,S,H).main(initial) : real]
 <= 1 * Pr[MultiUserEUFCMAGame(BSignOriginOperationDirect(A,H),S).main(initial)]
  + 1 * Pr[MultiUserEUFCMAGame(BSignOriginFactWitness(A,H),S).main(initial)]
  +     Pr[NodeCollisionGame(BHashOrigin(A,S),H).main(initial)]
  + 0
```

The left side is the exact real unauthorized-acceptance bit produced by the
origin-aware A0 environment after executing the shared production validator.
The right side contains only probabilities of named primitive games run with
named reduction adversaries. The operation- and fact-signature reductions use
one native multi-user experiment, so their guessing factors are exactly one.
The model-level canonical-encoding failure term is proved equal to zero.

This is a reduction theorem, not an unconditional claim that the primitive
probabilities are negligible. Concrete security follows only after instantiating
and validating the deployed signature and node-hash constructions against those
exact games.

## A0--A5 chain

### A0: real validator and win event

`UnauthorizedOriginGame.ec` gives the adaptive adversary protocol-shaped
operation-signing, authorization-fact-signing, and candidate-submission
procedures. Candidate submissions contain arbitrary operation bytes,
signatures, signed grants/revocations, causal views, and malformed public
inputs. The game, not the adversary, runs `ValidateOperation`, computes exact
causal state, and sets the win bit.

An accepted operation is unauthorized only when at least one of the following
fails in its exact accepted context:

- operation-signature origin for the complete production transcript;
- exact-incarnation membership;
- the required capability for that incarnation;
- operation-kind/capability binding;
- operation-body policy.

A malicious operation deliberately signed and issued by a genuinely authorized
principal is outside this win event.

### A1: canonical transcript and node collision

`CanonicalEncoding.ec` proves model-level injectivity of canonical operation
encoding. `UnauthorizedOriginHashReduction.ec` logs the complete production
node material—full transcript plus signature—and `BHashOrigin` returns the
actual distinct pair whose digests collide. The final theorem uses the exact
`NodeCollisionGame` probability.

### A2: operation-signature origin

`OriginOperationDirectInvariant.ec` and
`OriginOperationDirectReduction.ec` retain the first accepted unoriginated
operation signature and prove exact equality with the named native multi-user
EUF-CMA game run by `BSignOriginOperationDirect`.

### A3: signed authorization ancestry

`OriginFactWitnessGame.ec` and `OriginFactReductionWitness.ec` retain the first
accepted unoriginated authorization-fact signature and prove exact equality
with the named native multi-user EUF-CMA game run by
`BSignOriginFactWitness`.

`AuthorizationAncestry.ec` and the mapped authorization development cover
membership grants, capability grants, membership revocations, capability
revocations, issuer authority in the fact's own context, exact incarnation
binding, observed-remove behavior, and retired-incarnation non-revival.

### A4: exact causal and authorization state

The validator binds every fact identifier to immutable exact fact content,
checks the complete predecessor closure, normalizes precisely the facts in that
closure, and compares an exact authorization-state digest.

`CausalClosureRepresentation.ec` proves the mapping between the executable
closure map and an independent list representation. The authorization mapping
is split across:

- `AuthorizationRepresentation.ec`;
- `AuthorizationLeanDeltaMapping.ec`;
- `AuthorizationLeanDeltaCongruence.ec`;
- `AuthorizationLeanFullReplay.ec`.

The load-bearing theorem
`authorization_policy_replay_matches_independent_lean_apply` connects the
EasyCrypt replay to the independent Lean-style observed-remove fold. The
recorded Lean authorization source blob is:

```text
55b138aa423f46db69d50d4427d89d67636c6281
```

### A5: ideal authorization

`UnauthorizedLeanIdeal.ec`, `UnauthorizedLeanCertifiedIdeal.ec`, and
`UnauthorizedIdeal.ec` execute the validator and independent authorization
certificate. `UnauthorizedOriginPartition.origin_ideal_probability_zero`
proves the ideal unauthorized event has probability exactly zero. The ideal
game is not reject-all: honest production acceptance remains reachable and is
proved separately.

## Non-vacuity and reduction-connectivity controls

The final entry point also prints the following controls:

- `HonestOperationContract.witness_honest_operation_accepted`: the concrete
  honest canonical edit is accepted by the production validator with
  probability one;
- `MutationProofs.noncanonical_rejection_probability_one`: a concrete
  noncanonical operation is rejected with the exact canonical-reencoding
  failure and probability one;
- `PrimitiveControlProofs.test_signature_multi_user_eufcma_probability_one`:
  the intentionally insecure test signature scheme loses the exact primitive
  game with probability one, demonstrating that the signature reduction is
  connected to its primitive challenge.

The checker-proved one-defense-removed differential matrix is:

1. `MutationGameProofs.mutation_operation_signature_wins_probability_one`;
2. `MutationEditProofs.mutation_author_key_wins_probability_one`;
3. `MutationEditProofs.mutation_incarnation_wins_probability_one`;
4. `MutationEditProofs.mutation_document_wins_probability_one`;
5. `MutationEditProofs.mutation_domain_wins_probability_one`;
6. `MutationPolicyProofs.mutation_body_wins_probability_one`;
7. `MutationPolicyProofs.mutation_capability_wins_probability_one`;
8. `MutationPolicyProofs.mutation_context_wins_probability_one`;
9. `MutationPolicyProofs.mutation_digest_wins_probability_one`;
10. `MutationPolicyProofs.mutation_predecessor_wins_probability_one`;
11. `MutationHistoryProofs.mutation_recipient_wins_probability_one`;
12. `MutationHistoryProofs.mutation_merge_wins_probability_one`;
13. `MutationHistoryProofs.mutation_region_wins_probability_one`;
14. `MutationHistoryProofs.mutation_segment_wins_probability_one`.

Each module proves both the unmodified production rejection and the matching
single-defense-removed acceptance through the actual differential validator.


## BeeKEM KI-DCGKA foundation

`BeeKemInterfaceProof.ec` is the public checker target for the BeeKEM branch.
Its dependency closure contains 23 EasyCrypt sources and reaches the following
executable objects rather than a collection of unconstrained theorem
parameters:

- `BeeKemTypes.ec`: protocol state, operations, messages, personal secrets,
  group secrets, deliveries, and finite-retention state;
- `BeeKemQueryLog.ec`: one append-only record for every accepted or rejected
  state-transition or safety-relevant adversarial query;
- `BeeKemProtocol.ec`: the stateful Figure 8/9 create, add, remove, update,
  deliver, reveal, challenge-opening, compromise, and message-read procedures;
- `BeeKemSafety.ec`: the executable finite-`kappa` FSU, PCS, and CFS clauses and
  their conjunction over every successful challenge/compromise pair;
- `BeeKemKiGame.ec`: the hidden-bit KI-DCGKA game, final adversary guess, exact
  same-length uniform random challenge branch, and game evidence;
- `BeeKemPrimitiveGames.ec`: named HKR-CKS NIKE and multi-user CPA
  symmetric-encryption games;
- `BeeKemConstruction.ec`: one `BEEKEM_PAPER_INSTANCE` whose protocol, NIKE,
  sampler, and symmetric-encryption adapters are definitionally tied to the
  same BeeKEM construction;
- `BeeKemKiInterface.eca`: the single imported BeeKEM Theorem 1 boundary.

The adversary receives the complete KI oracle surface. The challenger—not the
adversary—computes acceptance, delivery readiness, reveal history, compromise
snapshots, the `bee_safe_kappa` predicate, and the challenge/member-addition
counters.

### Query history and safety

Every create, add, remove, update, deliver, reveal, challenge, and compromise
attempt is logged with its actual accepted bit and rejection reason. Figure 8's
perpetual read-only access to the control and direct message maps is modeled as
a direct read and is not counted as a safety query. An operation-bearing
successful query maps to its recorded operation.
A successful snapshot compromise maps to the actor's challenger-maintained
causal frontier at that instant. Rejected queries and successful queries with
no operation/frontier contribution map to the empty set.

The finite-`kappa` safety predicate then evaluates the complete log:

- FSU searches for `kappa` successful causally ordered updates between the
  challenged operation and a later compromise;
- PCS searches for a successful healing update between a compromise and the
  challenge;
- CFS requires `kappa` updates ending at the compromise together with pairwise
  causal concurrency between the challenge operation and the compromise
  frontier.

These are finite recursive predicates over challenger state. No adversary
supplies a `safe`, `admissible`, `q2op`, ancestry, reveal-history, or retention
Boolean.

### Public imported theorem

The sole BeeKEM axiom is
`beekem_theorem1_imported_normalized`. The checker prints its quantifier order
as:

```text
for every KI adversary A,
for every single concrete BeeKEM PaperInstance,
for every memory and public game-parameter tuple satisfying the side conditions,
there exist primitive adversaries BNike and BSe such that

AdvKI(BeeKemKiGame(A, PaperInstance))
 <= c * ceil(log2(n)) *
      (AdvHKR-CKS(BNike) + AdvMU-CPA(BSe)).
```

That order is load-bearing. `BNike` and `BSe` are existential witnesses after
the universally quantified challenged adversary and paper instance. They can
therefore be the Appendix-B constructions `B(A, Pi)` and `C(A, Pi)`; they are
not unrelated universal primitive adversaries. The KI game and both
right-hand-side games use adapters of the same `BEEKEM_PAPER_INSTANCE`.

The theorem side conditions are explicit:

- finite `kappa >= 1`;
- nonnegative challenge bound `c`;
- executable `beekem_is_ceil_log2 n h`;
- probability-one NIKE symmetry and symmetric-encryption correctness;
- probability-one evidence that the actual accepted challenge count is at most
  `c` and actual member-addition count is at most `n`.

The probability-one correctness premises are an honest, narrower
perfect-correctness specialization of the paper's overwhelming-correctness
formulation. Correctness failure has not been silently deleted.

### Advantage convention

The definition printed immediately before BeeKEM Theorem 1 calls raw game
success probability an advantage, while Appendix B reasons with absolute
differences between neighboring game probabilities. Raw success cannot satisfy
the displayed bound when `n = 1`, because the multiplier
`ceil(log2(1))` is zero.

The imported boundary therefore records one centered convention for all three
games:

```text
abs(Pr[guess = hidden bit] - 1/2).
```

Using the same factor-two alternative for every game scales both sides equally
and leaves the theorem's reduction factors unchanged. No raw-success theorem is
assumed.

### Imported and checked boundary

Machine-checked in this repository:

- the typed state and complete oracle environment;
- accepted/rejected query logging;
- finite-retention compromise responses;
- `q2op` frontier lifting and all three finite-`kappa` safety clauses;
- the hidden-bit KI game and exact random challenge branch;
- actual challenge and member-addition counters;
- named HKR-CKS and multi-user CPA games;
- same-instance protocol/primitive adapters;
- the theorem's quantifier shape and side conditions;
- positive and negative trace witnesses and mutation controls.

Imported from BeeKEM Theorem 1 and Appendix B:

- the cryptographic hybrid argument itself;
- the internal algorithms of the existential reductions `BNike` and `BSe`;
- the resulting inequality under the stated primitive assumptions.

This is a concrete formal interface to the paper theorem, not a
machine-checked reproof of Appendix B.

### BeeKEM non-vacuity and anti-regression controls

The public entry point prints checker-proved witnesses that exercise:

- real and random KI challenge branches;
- a wrong final guess changing the result;
- nonzero accepted challenge and member-addition counters;
- each FSU, PCS, and CFS positive trace and its unsafe boundary;
- missing healing updates, missing fork updates, ignored compromise history,
  ignored ancestry, ignored reveal history, and disabled finite retention;
- deliberately insecure-but-correct NIKE and symmetric encryption losing their
  named primitive games with probability one;
- counter mutations changing the theorem multiplier.

CI additionally performs two destructive source mutations:

1. it removes the existential `BNike` witness and requires the anti-cheating
   audit to reject the theorem boundary for that exact reason;
2. it deletes `BeeKemSafety.ec` and requires the pinned EasyCrypt compiler to
   reject the public closure because that dependency is genuinely required.

## Imported assumptions

The Deliverable A closure, checked through `ComputationalProof.ec`, contains
**zero imported axioms**. Its exact operation-signature, fact-signature, and
collision experiments remain explicit on the final theorem's right-hand side.

The separate BeeKEM closure, checked through `BeeKemInterfaceProof.ec`,
contains **exactly one imported axiom**:
`beekem_theorem1_imported_normalized`. That axiom is limited to BeeKEM
Theorem 1's Appendix-B reduction inequality with the explicit quantifier,
same-instance, correctness, safety, and query-bound conditions above. No
application final game or authorization advantage appears in it.

`ASSUMPTION_MANIFEST.json` records both proof boundaries, the exact named games,
the source-paper hash, the sole imported declaration, its non-claims, and the
remaining implementation-correspondence obligations.

## Checker evidence

The first complete theorem-bearing checkpoint is:

```text
source commit: 0dafe7d02d1afe8bbdffc4cd4e47c36543b8ed71
workflow run:  https://github.com/blinding-pixels/protocol-experiment/actions/runs/33284649082
artifact:      easycrypt-full-evidence-33284649082-1
artifact SHA:  sha256:4ee45fa1ee093df2ae28a0c33730d9b7eaf6ba4b17cf936c007f95af9452d831
```

That run recorded:

- anti-cheating audit exit status `0`;
- executable reference-suite exit status `0`;
- EasyCrypt checker exit status `0`;
- `65` EasyCrypt source files audited;
- `0` manifest axioms;
- `20` executable reference tests passed;
- `ComputationalProof.ec` as the diagnostic target;
- the immutable EasyCrypt image digest listed below.

The machine-readable manifest checkpoint also passed the complete closure:

```text
source commit: a1778b5d2b295af765da8baf0679c1c173539819
workflow run:  https://github.com/blinding-pixels/protocol-experiment/actions/runs/33284779030
artifact SHA:  sha256:22db093e933a3c32624f62827a06673c166ba827964c28e9374e83e2712d4e04
```


### BeeKEM theorem-boundary evidence

The checker-accepted theorem source and its later anti-regression guards are:

```text
theorem source commit:   54bc3b7653462f8ddf74d348ed9173523917c067
quantifier audit commit: d2cca0a57f55a4d35adf1b6faf3b3f2921d42e33
CI mutation commit:      e916660879de633c98d9d5e86d82ef8e894e650c
workflow run:            33340568672
artifact:                easycrypt-full-evidence-33340568672-1
artifact ID:             9740421932
artifact digest:         sha256:b21c28477007240363a30c4f70d2572c51fa47875e67f0985154c50c1c174ac0
```

That exact run recorded:

- source identity, paper hash, dependency closure, and source-manifest hashes;
- `88` EasyCrypt sources audited and exactly `1` manifest axiom;
- `20` executable reference tests passed;
- pinned EasyCrypt compilation of `BeeKemInterfaceProof.ec` with status `0`;
- theorem-boundary mutant audit status `1` and expected-rejection assertion
  status `0`;
- dependency-removal mutant checker status `1` and expected-rejection assertion
  status `0`;
- immutable EasyCrypt image
  `sha256:84980006e8b01fe6497bbd0ecd67deeb5e7361d8ad17e27d24924122d368e0fc`;
- EasyCrypt `r2026.07` and Why3 `1.8.2`.

The evidence artifact contains the exact checked sources, checker output,
mutation outputs, status files, source hashes, and extracted fixed-hash paper.

## Scope and remaining faithfulness work

The Deliverable A theorem is a suffix security game parameterized by an
arbitrary materialized `protocol_state`. That state represents the public DAG,
immutable fact-content
registry, exact fact closures, and application-policy expectations at the start
of the attack. The adversary then adaptively signs protocol-shaped objects and
submits arbitrary operations and views while accepted operations update the
state.

The complete handoff's larger shared application
`CreateGroup`/delivery/add/remove/grant/revoke trace API is not claimed by the
Deliverable A suffix theorem. The BeeKEM foundation does model its own Figure 8
create/add/remove/update/deliver/reveal/challenge/compromise interface, but it
has not yet been composed with the application authorization suffix game.
That composition remains an explicit faithfulness task before reusing both
pieces inside the live- and content-key games.

The following implementation obligations also remain outside this EasyCrypt
result:

- byte-for-byte correspondence between `CanonicalWire` and deployed Rust
  serialization;
- correspondence between `ExactAuthorizationDigest` and the deployed digest
  serialization/hash;
- concrete signature-scheme and node-hash security instantiation;
- Rust persistence, crash recovery, erasure, zeroization, and operating-system
  residue behavior;
- live application-key indistinguishability;
- ungranted content-key indistinguishability after the erasure frontier.

Accordingly, Deliverable A's authorization reduction and the BeeKEM
KI-DCGKA foundation are checker-accepted within their stated boundaries. The
BeeKEM result supplies the exact cryptographic base game and imported Theorem 1
interface that Deliverables L and C must reduce to; it does not itself prove
either application-key theorem.

This is not a claim that the entire three-deliverable computational handoff or
the concrete Rust implementation is complete.

## Running the checks

From the repository root:

```text
python3 tools/easycrypt/audit_computational.py

python3 -m unittest discover \
  -s formal/current-source/easycrypt/computational \
  -p 'test_*.py' -v
```

The branch-specific authoritative EasyCrypt targets are:

```text
formal/easycrypt-beekem-interface        BeeKemInterfaceProof.ec
other computational-proof branches      ComputationalProof.ec
```

CI uses:

```text
ghcr.io/easycrypt/ec-test-box:r2026.07
sha256:84980006e8b01fe6497bbd0ecd67deeb5e7361d8ad17e27d24924122d368e0fc
```

A checker-acceptance claim is valid only for the exact source commit, dependency
closure, source hashes, immutable image digest, audit output, mutation outputs,
and zero real-checker exit status in a captured workflow artifact. An expected
nonzero mutant status is successful only when its separate assertion status is
zero and the logged failure matches the intended mutation. Any later
proof-source change requires new evidence.
