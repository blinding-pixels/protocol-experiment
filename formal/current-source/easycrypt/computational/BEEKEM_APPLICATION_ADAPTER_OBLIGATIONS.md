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

## Read-only coordination refresh

The requested public files were inspected at the commit above. Since the prior
application-side snapshot
`ab8a8e6337081e206df5de5d7ba56c2b9d360283`, the BeeKEM foundation made one
material public-interface correction and then restored all mutation/counter
proofs against that corrected interface:

- `beekem_group_secret` is now a concrete `bool list` carrier rather than an
  integer-like wrapper;
- the KI game extracts the real secret bits and samples the random branch with
  `dlist dbool` at exactly the same length;
- the external `BEEKEM_GROUP_SECRET_SAMPLER` parameter was removed;
- the authoritative game is now instantiated as `BeeKemKiGame(A, P)`, and the
  imported Theorem 1 boundary uses that game directly;
- the complete safety mutations, exact challenge/member-addition counters, and
  Theorem 1 loss controls remain connected to the executable KI game.

These are foundation-side corrections and controls, not application-side
adapter proofs. In particular, the application wrapper may neither choose the
random challenge distribution nor convert its provisional integer root into an
authoritative group-secret bitstring by definitional identification.

## Authoritative surface observed on the parallel branch

The parallel branch currently exposes:

- concrete BeeKEM users, groups, operation IDs, per-author counters, control and
  direct-message maps, member states, retained personal secrets, operation DAG,
  delivery records, exact query counters, and bitstring group secrets in
  `BeeKemTypes.ec`;
- `create_group`, `add_member`, `remove_member`, `send_update`, `deliver`,
  `reveal`, `challenge`, `compromise`, and read access to control/direct messages
  through `BEEKEM_KI_ORACLES` in `BeeKemKiGame.ec`;
- a challenger-maintained query log recording every attempted query, acceptance,
  rejection reason, addressed counter/operation, and actor/target causal
  frontiers in `BeeKemQueryLog.ec` and `BeeKemProtocol.ec`;
- the finite, executable `bee_safe_kappa kappa operations queries` predicate in
  `BeeKemSafety.ec`, including ordered update-chain FSU, PCS, and concurrent-fork
  CFS clauses;
- an internally sampled same-length random challenge branch in
  `BeeKemKiGame.ec`; and
- a single imported boundary,
  `beekem_theorem1_imported_normalized`, over the executable KI game and named
  HKR-CKS/MU-CPA games in `BeeKemKiInterface.eca`.

## Explicit mapping obligations

1. **Principal and group identities.** Define injective application mappings
   from `principal` and the application document/group context to
   `beekem_user` and `beekem_group`. Do not identify wrappers merely because
   their provisional representations look similar.

2. **Application node addressing.** Map every accepted application BeeKEM
   control node to the authoritative `(beekem_user, beekem_counter)` message key
   and `beekem_operation_id`. Prove uniqueness and preserve the authoritative
   control message returned by `get_control_message`.

3. **Operation translation.** Show that application create, add, remove, and
   update calls correspond to the matching authoritative procedures and that
   the resulting operation author, target, kind, direct predecessors, complete
   ancestry, and per-author counter agree. The provisional digest parameter is
   application metadata, not an argument of the authoritative BeeKEM oracle.

4. **Delivery and responses.** Translate application delivery to the
   authoritative sender/counter/recipient call. Preserve causal readiness,
   direct-message selection, response operations, recipient frontiers, and the
   separate sender/response secret outputs. The provisional one-message/one-head
   model is not sufficient evidence for this obligation.

5. **Secret-output representation.** Relate provisional `beekem_secret option`
   to authoritative `beekem_secret_output`, distinguishing `BeeSecretValue`,
   `BeeSecretNoOutput`, and `BeeSecretUndefined`. For `BeeSecretValue`, define an
   explicit application-root representation relation to the authoritative
   `bool list`; prove the properties used by the key schedule. Do not cast the
   provisional integer carrier to the authoritative bitstring or collapse the
   three output cases.

6. **Random-branch ownership.** An application challenge must invoke the
   authoritative `challenge` procedure. The application adapter must not accept
   a sampler parameter, sample a replacement root itself, or preselect the
   random branch. Same-length random sampling belongs exclusively to the
   authoritative KI game and must remain tied to the real challenged secret's
   bit length.

7. **Reveal and challenge exclusions.** Prove that each accepted application
   reveal/challenge addresses the same authoritative sender/counter entry and
   that the authoritative challenge mark and challenge counter change exactly
   once. The application must never return the raw `beekem_group_secret`.

8. **Snapshot compromise.** Map an application compromise to the full
   authoritative `beekem_member_state option`. Its `q2op` image is the
   challenger-recorded causal frontier, which may contain multiple concurrent
   operations; a single application head is not generally equivalent.

9. **Complete query log.** Construct the authoritative `beekem_query_log` from
   actual oracle execution, including failed attempts and rejection reasons.
   The current successful-only `live_query` list is not equivalent. Prove order,
   kind, actor, target, counter, operation, frontier, acceptance, and rejection
   preservation entry by entry.

10. **Exact safety bridge.** Prove that an accepted application challenge yields
    a successful authoritative challenge query and that the complete resulting
    log satisfies the imported `bee_safe_kappa`. This must use the ordered update
    chain and conservative frontier lifting in `BeeKemSafety.ec`; the provisional
    count-based predicate is not a substitute.

11. **Game and loss alignment.** Relate application challenge count and member
    additions to `bke_challenge_count` and `bke_member_addition_count`, then apply
    `beekem_theorem1_imported_normalized` with the exact executable side
    conditions. Instantiate the authoritative two-parameter KI game; do not
    reintroduce the deleted sampler, import a second theorem, or reconstruct
    Appendix B.

## Stable composition seam

`LivePrfReduction.ec` is intentionally parameterized by the application
`BEEKEM_LIVE_RUNTIME`. It consumes roots only through the existing production
key-schedule calls and treats application admissibility as an external
challenger-computed gate. After the parallel branch is merged, the final
application/BeeKEM adapter should replace that runtime and the provisional
admissibility implementation. The representation bridge must deliver only the
real authoritative root to the application key schedule; hidden-bit sampling
must remain inside the authoritative KI challenge. The PRF oracle,
history-query simulation, `BPRFLive`, hidden-bit normalization, and ideal-game
reasoning should not need structural rewrites.
