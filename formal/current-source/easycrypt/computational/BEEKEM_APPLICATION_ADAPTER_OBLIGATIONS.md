# BeeKEM application adapter obligations

Status: provisional application-side record. The authoritative BeeKEM
foundation is now present through the merge on `main`; this document records
the remaining adapter obligations.

`BeeKemKiInterface.eca` is the authoritative theorem boundary.
`LiveBeeKemKiInterface.eca`, `LiveBeeKemControl.ec`,
`LiveBeeKemDerived.ec`, `LiveBeeKemOracle.ec`, and `LiveBeeKemReduction.ec` remain
provisional scaffolding. They are not the paper-authoritative KI-DCGKA game or
`bee_safe_kappa` definition, and no Deliverable L completion claim may depend on
them until the obligations below are discharged against the merged foundation.

## Current authoritative direction

The last green BeeKEM foundation already establishes the following application
integration direction:

- `beekem_group_secret` is a concrete bitstring carrier;
- the KI game samples the random challenge internally at the exact real-secret
  length;
- the external group-secret sampler has been removed;
- one `BEEKEM_PAPER_INSTANCE` supplies the protocol, NIKE, NIKE sampler, and
  symmetric-encryption adapters;
- the challenger owns the complete attempted-query log, causal frontiers,
  reveal/challenge admission marks, exact challenge and member-addition
  counters, finite retention state, and exact `bee_safe_kappa` computation;
- FSU, PCS, concurrent-fork CFS, compromise-log, causal-ancestry, reveal-log,
  finite-retention, and counter-factor mutations reach the executable KI game;
  and
- the sole imported reduction boundary is
  `beekem_theorem1_imported_normalized`.

The two newer red heads add a semantically important interface refinement. They
replace free-standing primitive-reduction adversaries with typed constructors:

```text
BEEKEM_THEOREM1_NIKE_REDUCTION(A, I, O)
BEEKEM_THEOREM1_SE_REDUCTION(A, I, O)
```

The intended Appendix-B witnesses are therefore constructed from the exact KI
adversary `A` and exact paper instance `I`, rather than being unrelated modules
with matching primitive-game signatures. This is the correct direction for the
final application theorem, but it is not yet an imported premise because its
current EasyCrypt closure is red.

## Imported-boundary normalization blocker

The current parallel branch computes

```text
beekem_ki_final_win safe protocol_failure guess bit
  = safe /\ (protocol_failure \/ guess = bit)
```

but defines

```text
beekem_normalized_ki_advantage p = abs(p - 1/2).
```

Those choices do not compose for arbitrary `BEEKEM_KI_ADVERSARY` modules. An
adversary whose complete trace is unsafe in both hidden-bit branches has
`Pr[win] = 0`, while the stated centered operator assigns value `1/2`. The
foundation's executable unsafe traces make this a reachable semantic issue, not
a hypothetical one.

The imported theorem currently has neither an all-safe premise nor a safe-mass
baseline. Deliverable L must not instantiate it until the BeeKEM branch resolves
this in one authoritative, checker-connected way. This application branch does
not choose the BeeKEM security notion on the foundation's behalf.

## Explicit mapping obligations

1. **Principal and group identities.** Define injective application mappings
   from `principal` and application document/group context to `beekem_user` and
   `beekem_group`. Do not identify wrappers merely because provisional
   representations look similar.

2. **Application node addressing.** Map every accepted application control node
   to the authoritative `(beekem_user, beekem_counter)` message key and
   `beekem_operation_id`. Prove uniqueness and preserve the exact control and
   direct messages returned by the authoritative read procedures.

3. **Operation translation.** Show that application create, add, remove, and
   update calls correspond to the matching authoritative procedures and that
   author, target, operation kind, direct predecessors, complete ancestry, and
   per-author counter agree. Application authorization metadata is not an
   argument to the BeeKEM protocol oracle.

4. **Delivery and responses.** Translate application delivery to the
   authoritative sender/counter/recipient call. Preserve causal readiness,
   direct-message selection, response operations, recipient frontiers, and the
   distinct sender and response secret outputs.

5. **Secret-output representation.** Relate provisional `beekem_secret option`
   to `beekem_secret_output`, distinguishing `BeeSecretValue`,
   `BeeSecretNoOutput`, and `BeeSecretUndefined`. For `BeeSecretValue`, define an
   explicit representation relation from the authoritative bitstring root to
   the application key-schedule root. Do not cast carriers or collapse cases.

6. **Random-branch ownership.** Every application challenge must invoke the
   authoritative `challenge` procedure. The adapter must not sample a
   replacement root, choose the random branch, or reintroduce an external
   sampler.

7. **Reveal and challenge exclusions.** Prove that accepted application reveal
   and challenge calls address the same authoritative sender/counter entry and
   preserve the shared exclusion mark and exact challenge counter. The
   application must never return the raw BeeKEM group secret.

8. **Snapshot compromise.** Map application compromise to the complete
   authoritative member state. Its `q2op` image is the challenger-recorded
   causal frontier and may contain several concurrent operations.

9. **Complete query log.** Preserve every oracle attempt, including failures and
   rejection reasons. Prove order, kind, actor, target, counter, operation,
   actor/target frontier, acceptance, and rejection preservation entry by entry.
   The provisional successful-only application list is not equivalent.

10. **Exact safety bridge.** Prove that each accepted application challenge
    becomes one successful authoritative challenge and that the complete
    resulting log satisfies exact `BeeKemSafety.bee_safe_kappa`. This must use
    ordered FSU/PCS/CFS chains and conservative frontier lifting, not a supplied
    Boolean or the provisional count-based predicate.

11. **Construction and reduction binding.** Prove the final adapter runtime
    corresponds to `BeeKemProtocolOfPaperInstance(PaperInstance)`. The NIKE and
    SE reductions imported for the final theorem must be the typed constructors
    applied to the exact application-derived KI adversary and the same paper
    instance.

12. **Game, normalization, and loss alignment.** Relate actual application
    challenge count and member additions to `bke_challenge_count` and
    `bke_member_addition_count`, resolve the normalization blocker, then apply
    the green imported theorem with its exact executable side conditions. Do
    not import a second theorem or reconstruct Appendix B.

## Application-side progress independent of the blocker

The checked `ComputationalProof.ec` closure now contains:

- Deliverable A authentication-loss composition;
- the application multi-domain PRF reduction and exact fixed-bit hop;
- the bit-free ideal game and ideal-live-key advantage zero;
- exact transcript injectivity for live, history, and constrained-history
  queries;
- live/history and live/constrained-history domain-collapse mutations;
- single-field omission mutations for the BeeKEM root, protocol version,
  document identifier, node identifier, and authorization digest;
- a zero-safe-mass normalization control;
- a two-accepted-challenge trace whose primitive PRF transcript contains exactly
  two challenge calls; and
- differential controls for both reveal/challenge exclusion directions:
  reveal-then-challenge and challenge-then-reveal.

Each mutation changes only its named cryptographic or admission condition while
retaining the complete typed transcript and all other checks. These are
application-composition controls, not claims that the provisional BeeKEM
runtime is authoritative.

## Stable composition seam

`LivePrfReduction.ec` remains parameterized by `BEEKEM_LIVE_RUNTIME`. It consumes
roots only through the production key-schedule interface and treats
admissibility as challenger-computed state. After the parallel branch is green
and merged, the authoritative adapter should replace that runtime and the
provisional safety implementation without structural rewrites to the PRF
oracle, history-query simulation, `BPRFLive`, hidden-bit algebra, or ideal game.

A green application workflow for this document proves only the already printed
intermediate theorems and controls. It is not a Deliverable L completion claim.
