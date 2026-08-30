# BeeKEM coordination snapshot for Deliverable L

Application branch: `formal/easycrypt-live-key-reduction`

Read-only BeeKEM branch: `formal/easycrypt-beekem-interface`

Exact BeeKEM source inspected: `fda87857acfa0875509b577cc02afedafee397f0`

Exact BeeKEM workflow inspected: `33338655869`

Evidence artifact: `easycrypt-full-evidence-33338655869-1`

Evidence artifact SHA-256:
`8ee813027c4ada0b938a623fbb4128322bf250bd07e55e765cae685e002107af`

This file records an application-side, read-only coordination snapshot. It does
not merge, cherry-pick, restate, or replace the BeeKEM foundation.

## Current BeeKEM checker state

The exact BeeKEM head above is checker-accepted by the pinned workflow:

- `BeeKemInterfaceProof.ec` compiled successfully under the immutable EasyCrypt
  image;
- the dependency closure contained 23 source files and included
  `BeeKemSafety.ec`;
- the computational audit covered 88 EasyCrypt sources and found the one
  manifest-declared imported BeeKEM theorem axiom;
- all 20 executable reference tests passed; and
- deleting `BeeKemSafety.ec` from the copied dependency closure made the checker
  fail for the expected missing-theory reason.

The earlier EasyCrypt module-substitution anomaly observed at
`a360e933b8cf1bf61ab85532f590427e950d9256` is resolved. The current foundation
uses one flat `BEEKEM_PAPER_INSTANCE` module and derives the protocol, NIKE,
NIKE-sampler, and symmetric-encryption adapters from that same instance.

## Current authoritative public surface

The foundation currently owns and checker-connects:

- concrete bitstring BeeKEM group secrets;
- same-length random challenge sampling inside the KI challenger;
- the complete attempted-query log, including rejected calls and causal
  frontiers;
- exact finite-kappa `bee_safe_kappa` over that log and the operation DAG;
- exact challenge and member-addition counters;
- stateful Reveal/Challenge exclusion for the same sender/counter entry;
- finite personal-secret retention and compromise exposure;
- FSU, PCS, concurrent-fork CFS, compromise-log, and causal-ancestry mutation
  witnesses connected to the actual KI game;
- nonzero challenge-count and logarithmic member-addition loss-factor controls;
- executable NIKE and symmetric-encryption primitive games; and
- the sole imported BeeKEM Theorem 1 boundary,
  `beekem_theorem1_imported_normalized`.

The theorem boundary now quantifies one `BEEKEM_PAPER_INSTANCE`. The KI protocol,
HKR-CKS game, MU-CPA game, NIKE symmetry premise, and symmetric-encryption
correctness premise are all instantiated through adapters derived from that
same module. The application adapter must therefore target the exact protocol
adapter of one paper instance; matching procedure signatures alone is not an
equivalence proof.

## Normalization blocker remains open

The current BeeKEM game still computes

```text
beekem_ki_final_win safe protocol_failure guess bit
  = safe /\ (protocol_failure \/ guess = bit)
```

while its public advantage operator is

```text
beekem_normalized_ki_advantage p = abs(p - 1/2).
```

Those choices do not compose for arbitrary KI adversaries without an additional
safety premise or a safe-mass baseline. An adversary whose complete trace is
unsafe in both branches loses with probability one, so `Pr[win] = 0`, but the
current centered operator assigns value `1/2`. The foundation's own mutation
witnesses make unsafe losing traces executable, so this is not merely a
syntactic concern.

Deliverable L must not instantiate the imported theorem until the BeeKEM branch
resolves this in one authoritative, checker-connected way. This application
branch does not choose the BeeKEM security notion on the foundation's behalf.

## Application-side progress independent of the blocker

The full `ComputationalProof.ec` closure now contains:

- the Deliverable A authentication-loss composition;
- the concrete application multi-domain PRF reduction;
- the bit-free ideal game and exact ideal-zero theorem;
- exact transcript injectivity for live, history, and constrained-history
  queries;
- live/history and live/constrained-history domain-collapse mutations;
- prior-live-reveal challenge-exclusion mutation;
- zero-safe-mass normalization controls; and
- single-field omission mutations for the BeeKEM root, protocol version,
  document identifier, node identifier, and authorization digest.

Each omission mutation changes only its named cryptographic input while the
complete typed transcript still records the differing value. In every case the
insecure schedule wins with probability one and has normalized advantage one
half. These are application-composition controls, not claims that the
provisional BeeKEM runtime is authoritative.

## Remaining adapter obligations affected by this snapshot

1. Map application principals and group/document identities injectively to
   authoritative BeeKEM users and groups.
2. Map each accepted application control node to the authoritative
   `(beekem_user, beekem_counter)` key and `beekem_operation_id`, preserving the
   returned control/direct messages and response operations.
3. Translate create, add, remove, update, delivery, reveal, challenge, and
   compromise through the authoritative procedures while preserving every
   attempted query, rejection, actor/target frontier, and query order.
4. Preserve `BeeSecretValue`, `BeeSecretNoOutput`, and `BeeSecretUndefined`
   distinctly and prove an explicit representation relation from the
   authoritative bitstring root to the application key-schedule root.
5. Preserve the shared Reveal/Challenge admission mark, exact challenge counter,
   finite retention, and full compromise frontier.
6. Prove every accepted application challenge becomes one successful
   authoritative challenge and that the complete resulting log satisfies exact
   `BeeKemSafety.bee_safe_kappa`; do not assume this as a Boolean.
7. Prove that the adapter runtime corresponds to
   `BeeKemProtocolOfPaperInstance(PaperInstance)` for the exact paper instance
   used on both sides of Theorem 1.
8. Resolve the BeeKEM normalization blocker, relate actual application challenge
   and addition counts to the theorem side conditions, and only then instantiate
   `beekem_theorem1_imported_normalized`.
9. Expose the final L0--L4 theorem with the imported BeeKEM term, concrete
   multi-domain PRF term, ideal zero, and Deliverable A's named loss expansion.

A green application workflow for this snapshot proves only the printed
intermediate theorems and controls. It is not a Deliverable L completion claim.
