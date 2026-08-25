# BeeKEM primary-source audit

## Source inspected

- Derek Yen, Andrés Fábrega, Liangrun Da, Martin Kleppmann, John Mumm,
  Sunoo Park, and Brooklyn Zelenka, *BeeKEM: Decentralized, Secure and
  Efficient Group Key Agreement*, Cryptology ePrint Archive 2026/1434.
- PDF retrieved by CI from `https://eprint.iacr.org/2026/1434.pdf`.
- SHA-256 recorded by the verification workflow:
  `129a819400898536455cabe4ba104c02d902384ea802b4900a388e8e9c0e4fb3`.

## Answer to the primitive-instantiation question

BeeKEM does instantiate a finite-`kappa` cross-fork-secure DCGKA in the paper's
security model. It is not merely a definition or an assumed primitive.

The paper defines a key-indistinguishability game for DCGKA and a safety
predicate `bee-safe_kappa`. Its three clauses encode:

- `kappa`-forward secrecy with updates;
- post-compromise security;
- `kappa`-cross-fork security.

Theorem 1 states a concrete reduction for every integer `kappa >= 1`. For an
adversary making at most `c` challenge queries and at most `n` member additions,
the paper bounds its BeeKEM advantage by:

```text
c * ceil(log_2 n) * (Adv_NIKE^hkr-cks + Adv_SE^mu-cpa)
```

The full proof is given in Appendix B. Thus a finite-`kappa` base object exists
at the paper level under the stated NIKE and symmetric-encryption assumptions.

## The important threat-model limit

The phrase "actively secure `kappa`-cross-fork DCGKA" is stronger than what
BeeKEM Theorem 1 establishes unless "active" is defined narrowly.

BeeKEM assumes:

- users execute the protocol honestly;
- the adversary can choose network-delivery timing and create arbitrary
  partitions while respecting authenticated causal broadcast;
- the adversary can obtain snapshot compromises of user state;
- the adversary can issue reveal and challenge queries;
- authenticated causal broadcast prevents message modification, forged sender
  identities, and delivery that violates causal order.

Therefore BeeKEM covers an adversarial scheduler and adaptive snapshot
compromise in an authenticated causal-broadcast model. It does **not** prove
security against an authorized Byzantine group member who arbitrarily deviates
from the protocol, emits malformed cryptographic payloads, equivocates outside
the ACB abstraction, or selectively violates erasure.

The composition theorem must consequently choose one of two honest statements:

1. **BeeKEM-model theorem.** Assume honest protocol execution, ACB, and snapshot
   compromise exactly as in the BeeKEM game. Then BeeKEM is a concrete
   finite-`kappa` base primitive.
2. **Fully malicious-member theorem.** Assume or construct a DCGKA secure
   against arbitrary deviations by authorized insiders. BeeKEM Theorem 1 alone
   does not instantiate this stronger primitive.

## What `kappa` actually buys

BeeKEM retains the `kappa` most recent personal secrets. Larger `kappa` permits
recovery from older forks but enlarges the compromise exposure region.

- finite `kappa` gives `kappa`-CUC, `kappa`-FSU, and `kappa`-CFS;
- `kappa = 1` gives the strongest proved BeeKEM FSU/CFS point but the weakest
  fork-recovery window;
- full correctness under concurrency requires unbounded retention
  (`kappa = infinity`) and correspondingly weakens forward and cross-fork
  protection.

The paper also sketches `BeeKEM_FS`, a variant intended to obtain full FS and
CFS by sacrificing access to secrets created on forks. Section 7 presents this
as a sketch rather than a replacement for the proved finite-`kappa` theorem, so
this artifact does not use `BeeKEM_FS` as a verified base primitive.

## Interaction with the role-authorization layer

The role extension sits above the imported BeeKEM theorem. It does not modify
BeeKEM's key schedule, tree update, retained-personal-secret policy, or
`bee-safe_kappa` challenge predicate.

The composed protocol uses BeeKEM to establish the internal node secret `S_v`.
The application then derives domain-separated live and history namespaces and
validates public operations through a separate authenticated authorization
layer.

A capability-gated operation must be bound to:

```text
author
required capability
causal-context identifier
operation identifier and body
normalized authorization-state digest
signature and identity credential
```

The role layer can establish:

- a member without the required role cannot pass the modeled operation gate
  except through signature, identity-credential, role-credential, or transcript
  failures;
- accepted operations remain signed and attributable under those assumptions;
- observed membership and role tags can be tombstoned after an external
  detection decision;
- accepted audit evidence can survive that eviction.

None of those facts strengthens BeeKEM's malicious-member theorem. An authorized
role holder remains an authorized protocol user from BeeKEM's perspective.
Roles reduce who can issue a sensitive operation; they do not force a holder who
has the role to issue only benevolent operations or to follow erasure rules.

Therefore the combined theorem must not say:

> BeeKEM plus roles is secure against arbitrary Byzantine authorized members.

The honest statement is:

> Under BeeKEM's exact honest-execution/ACB game, and under separate sound
> identity, role, signature, transcript, and policy assumptions, unauthorized
> operations are rejected by the role layer and accepted operations are
> attributable. Arbitrary malicious behavior by a genuinely authorized role
> holder remains outside the imported BeeKEM theorem.

## Separation of role compromise from BeeKEM compromise

A role credential is public authorization evidence, not a BeeKEM node secret.
Compromise of a role-holder signing key or credential affects operation
authorization and attribution. Compromise of BeeKEM state affects the exposure
region defined by `bee-safe_kappa` and the composed history-retention rules.

These compromise classes must not be conflated:

- a stolen signing key may permit forged capability-gated operations without
  necessarily exposing past message keys;
- a BeeKEM snapshot compromise may expose live/cross-fork key material allowed
  by `E_kappa` without automatically forging another member's signature;
- a principal compromised in both dimensions contributes to both the operation
  authorization threat and the cryptographic exposure region.

The final computational model must state both oracle families explicitly.

## Consequence for this project

The first research seam is resolved as follows:

- **Existence under the BeeKEM game:** yes, instantiated and reduced to concrete
  assumptions.
- **Existence under arbitrary active malicious-member behavior:** not settled by
  BeeKEM 2026/1434.
- **Implementation with finite retention:** must be checked separately; a proof
  for every finite `kappa` does not establish that a particular implementation
  actually deletes all but `kappa` personal secrets.
- **Role-gated authorization:** composable as a separate authenticated public
  layer, but its computational security depends on identity/role credentials,
  signatures, canonical transcripts, and exact causal-context binding.
- **Malicious authorized role holder:** still outside the imported BeeKEM
  theorem; the achieved response is narrower authority, attribution, evidence,
  detection, and eviction.

The remaining cryptographic composition proof must inherit the exact
`bee-safe_kappa` challenge exclusions rather than invoking an undefined
"actively secure" primitive. It must separately account for operation-signing
and credential oracles instead of hiding authorization inside the BeeKEM
advantage term.

## 2026-08-25 assumption revalidation

The newly explicit assumptions do not change the BeeKEM paper theorem or its
finite-`kappa` threat model. They change only the composition and evidence
boundary around the imported result.

BeeKEM does not establish application role lifecycle semantics, canonical
public-state byte encoding, consistency-receipt persistence, production
rollback resistance, host erasure, or target timing behavior. The imported
cross-fork theorem therefore remains a conditional component of C-003 rather
than end-to-end implementation evidence.

### Current lifecycle theorem source

The current Lean lifecycle source is authored but kernel-pending. It states the
removal-only revival counterexample and the coupled-tombstone and fresh-incarnation
repairs without adding cryptography. Until the exact Lean 4.32.2 kernel accepts
`formal/current-source/CausalDagCgka/AuthorizationLifecycle.lean` under the existing
axiom audit, these are source-level candidate theorems backed by the executable
finite oracle, not newly kernel-checked results.
