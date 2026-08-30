# BeeKEM coordination snapshot for Deliverable L

Application branch: `formal/easycrypt-live-key-reduction`

Read-only BeeKEM branch: `formal/easycrypt-beekem-interface`

Exact BeeKEM source inspected: `a360e933b8cf1bf61ab85532f590427e950d9256`

Exact BeeKEM workflow inspected: `33337603316`

This file records an application-side coordination snapshot. It does not merge,
cherry-pick, restate, or replace the BeeKEM foundation, and it is not evidence
that the current BeeKEM head is checker-accepted.

## Current BeeKEM checker state

The source audit passed over 87 EasyCrypt sources with the one manifested
BeeKEM theorem axiom, and the 20 executable reference tests passed. The pinned
EasyCrypt compile of `BeeKemInterfaceProof.ec` failed while importing
`BeeKemKiInterface.eca` with:

```text
anomaly: File "src/ecSubst.ml", line 289, characters 2-8:
Assertion failed
```

The failure is in EasyCrypt module substitution for the new construction-bound
theorem surface. Therefore the exact head above is not yet an imported premise
available to Deliverable L.

The earlier application-side snapshot
`ec516a7e3c376dffb9d6d3872c26bb99d6a3a8b9` remains the last BeeKEM checkpoint
this branch recorded as pinned-checker green.

## Public interface changes since the earlier green snapshot

### Reveal admission control

`BeeKemRevealMutationProofs.ec` executes the exact KI oracle. In the production
trace, a successful Reveal marks `(sender, counter)` and the later Challenge of
the same entry is rejected without incrementing the challenge counter. The
single mutation clears only that shared mark after preserving the successful
Reveal in the append-only query log; the same Challenge then executes and
increments the real challenge counter.

The final application adapter must preserve this shared stateful exclusion. A
successful application reveal may not be represented only as an informational
log entry.

### Construction identity

`BeeKemConstruction.ec` introduces:

```text
BEEKEM_PAPER_CONSTRUCTION(Nike, Se)
```

The imported theorem source now defines its KI protocol as that construction
functor instantiated by the same NIKE and symmetric-encryption modules whose
HKR-CKS and MU-CPA games occur on the right-hand side.

This closes an important shape-level loophole: an unrelated module that merely
implements `BEEKEM_PROTOCOL_ALGORITHMS` must not be eligible for Theorem 1.
However, the current EasyCrypt substitution anomaly means this strengthened
boundary is not yet checker-accepted.

The final Deliverable L adapter must prove that its BeeKEM runtime and returned
roots correspond to the exact construction instance used by the imported
theorem. Equality of procedure signatures is not an equivalence proof.

## Unchanged authoritative requirements

The BeeKEM branch still owns:

- concrete bitstring group secrets;
- same-length random challenge sampling inside the KI challenger;
- the complete attempted-query log, including rejections and causal frontiers;
- exact `bee_safe_kappa` over that log and the operation DAG;
- actual challenge and member-addition counters;
- the NIKE and symmetric-encryption primitive games; and
- the sole imported BeeKEM Theorem 1 boundary.

The application branch must not sample a replacement root, create a competing
safety predicate, add a second BeeKEM axiom, or identify its provisional integer
root with the authoritative bitstring by representation coincidence.

## Normalization blocker remains open

The current BeeKEM game still gates final success by `safe`, while its public
centered operator subtracts an unconditional `1/2`. Consequently, an unsafe
trace that loses in both hidden-bit branches has success probability zero but
is assigned centered value one half.

Deliverable L must not instantiate Theorem 1 until the BeeKEM foundation chooses
and checker-connects one authoritative repair, such as a probability-one safety
premise or a safe-mass baseline. This application branch does not choose the
BeeKEM security notion on its behalf.

## Application-side progress independent of the blocker

The following application controls are in the full `ComputationalProof.ec`
closure:

- `LivePrfAuthorizationDigestMutation`: omitting only the authorization digest
  yields game success probability one and normalized advantage one half;
- `LivePrfRootBindingMutation`: omitting only the BeeKEM root yields game
  success probability one and normalized advantage one half; and
- `LivePrfEligibilityNormalizationControls`: a zero-query ineligible adversary
  has success probability zero, eligibility mass zero, and application PRF
  normalized advantage zero.

These results specify load-bearing application-composition behavior without
claiming the provisional BeeKEM wrapper is authoritative.

## Remaining adapter obligations affected by this snapshot

1. Map application principals, groups, nodes, and causal context injectively to
   authoritative BeeKEM users, groups, sender/counter message keys, operations,
   and frontiers.
2. Translate create, add, remove, update, delivery, reveal, challenge, and
   compromise through the authoritative procedures while preserving every
   attempted query and rejection.
3. Preserve the three distinct secret outputs and prove the explicit
   application-root relation to the authoritative bitstring secret.
4. Preserve the shared Reveal/Challenge admission mark and exact challenge
   counter transition.
5. Prove every accepted application challenge becomes a successful
   authoritative challenge and that the resulting complete log satisfies exact
   `BeeKemSafety.bee_safe_kappa`.
6. Prove the adapter runtime corresponds to the exact
   `BEEKEM_PAPER_CONSTRUCTION(Nike, Se)` instance used by Theorem 1.
7. Resolve the BeeKEM normalization and EasyCrypt substitution blockers before
   applying the imported theorem.
8. Relate actual application challenge/member-addition counts to the theorem
   loss and only then expose the final Deliverable L bound.

A green application workflow for this snapshot proves only that the existing
application proof closure remains intact. It does not make the red BeeKEM head
green and is not a Deliverable L completion claim.
