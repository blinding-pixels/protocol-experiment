# Computational proof development

Status: **Deliverable A's unauthorized-operation reduction theorem is checker-accepted. Deliverables L and C remain open.**

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

## Imported assumptions

The Deliverable A closure contains **zero imported axioms**. The exact
operation-signature, fact-signature, and collision experiments remain explicit
on the final theorem's right-hand side instead of being hidden behind arbitrary
real-valued advantage operators.

`ASSUMPTION_MANIFEST.json` records:

- the public theorem and its exact named games;
- factor one for both native multi-user signature reductions;
- the two proved-zero terms;
- zero imported assumptions;
- model contracts that still require concrete implementation correspondence.

BeeKEM is not imported by this authorization-only result.

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

## Scope and remaining faithfulness work

The theorem is a suffix security game parameterized by an arbitrary materialized
`protocol_state`. That state represents the public DAG, immutable fact-content
registry, exact fact closures, and application-policy expectations at the start
of the attack. The adversary then adaptively signs protocol-shaped objects and
submits arbitrary operations and views while accepted operations update the
state.

The complete handoff's larger `CreateGroup`/delivery/add/remove/grant/revoke
trace API is not claimed by this theorem. Integrating this suffix result into
that full shared trace environment remains an explicit faithfulness task,
particularly before reusing it inside the live- and content-key games.

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

Accordingly, Deliverable A's reduction theorem is checker-accepted within the
stated abstract/suffix-game boundary. This is not a claim that the entire
three-deliverable computational handoff or the concrete Rust implementation is
complete.

## Running the checks

From the repository root:

```text
python3 tools/easycrypt/audit_computational.py

python3 -m unittest discover \
  -s formal/current-source/easycrypt/computational \
  -p 'test_*.py' -v
```

The authoritative EasyCrypt checker target is `ComputationalProof.ec`. CI uses:

```text
ghcr.io/easycrypt/ec-test-box:r2026.07
sha256:84980006e8b01fe6497bbd0ecd67deeb5e7361d8ad17e27d24924122d368e0fc
```

A checker-acceptance claim is valid only for the exact source commit, source
hashes, immutable image digest, audit output, and zero checker exit status in a
captured workflow artifact. Any later proof-source change requires new evidence.
