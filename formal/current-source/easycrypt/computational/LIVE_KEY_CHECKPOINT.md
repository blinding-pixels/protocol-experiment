# Deliverable L live-key checkpoint

Exact branch: `formal/easycrypt-live-key-reduction`

This record describes the active, non-release Deliverable L state after the
application PRF and ideal-game checkpoints.

## Checker-connected results on this branch

- Deliverable A remains the previously checker-accepted origin-aware
  authorization reduction and is reused without a second signature/collision
  game clone.
- `LiveKeyGame.ec` contains the executable adaptive application trace and the
  production validator seam.
- `LiveAuthenticationReduction.ec` connects live authentication failure to
  Deliverable A's exact named operation-signature, authorization-fact-signature,
  and complete node-material collision games.
- `LivePrfApplicationReduction.ec` defines the concrete `BPRFLive` application
  reduction. Ordinary live reveals stay on the real schedule, only an accepted
  application challenge invokes the primitive live challenge, and both history
  domains are simulated through their typed real-domain procedures.
- `LivePrfApplicationHop.ec` proves equality of the authenticated application
  fixed-bit one-event and the corresponding multi-domain PRF game one-event,
  and therefore equality of their fixed-bit distinguishing distances.
- `LivePrfIdeal.ec` proves the application ideal live-key advantage is exactly
  zero by relational equivalence of the two fixed-bit projections.
- Application controls prove that every PRF oracle path is reachable, that a
  rejected application challenge consumes no primitive challenge and closes the
  wrapper switch, and that an intentionally insecure KDF loses the primitive
  game with probability one.

## Explicit provisional boundary

The legacy application-side operation
`LiveKeyGame.bee_safe_kappa` is retained only as namespaced provisional
scaffolding for the existing checker-connected application trace. It is a
successful-query, count-based gate and is **not** the paper's authoritative
`BeeKemSafety.bee_safe_kappa`. It must be deleted or replaced by the proved
adapter after the parallel BeeKEM foundation is merged; no final theorem may
apply BeeKEM Theorem 1 through this legacy operation.

The temporary `LiveBeeKemKiInterface.eca` file is likewise an
application-shaped seam, not the authoritative `BeeKemKiInterface.eca`. Its
declarations are not claimed identical or equivalent to the paper model's
types or procedures.

The paper-authoritative types, complete attempted-query log, causal-frontier
lifting, exact finite-kappa `bee_safe_kappa`, KI game, primitive games, and
Theorem 1 boundary are now present from the merged BeeKEM foundation. The exact
replacement obligations are in `BEEKEM_APPLICATION_ADAPTER_OBLIGATIONS.md`.

## Remaining Deliverable L work

- implement and prove the exact application-to-authoritative adapter;
- prove every accepted application challenge maps to a successful authoritative
  challenge and that the complete authoritative log satisfies exact
  `BeeKemSafety.bee_safe_kappa`;
- connect actual application challenge/member-addition counters to the imported
  BeeKEM Theorem 1 side conditions;
- add the live/history domain-collapse mutation control and remaining
  anti-triviality witnesses;
- expose the final L0--L4 theorem with the imported BeeKEM term, the concrete
  multi-domain PRF term, ideal zero, and Deliverable A's named loss expansion.

A green run at this stage proves only the printed intermediate theorems and
controls. It is not a Deliverable L completion claim.
