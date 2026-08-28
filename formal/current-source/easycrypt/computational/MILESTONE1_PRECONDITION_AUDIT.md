# Milestone 1 precondition audit

Date: 2026-08-26

## Canonical locations

- canonical repository: `blinding-pixels/protocol-experiment`
- base branch and audited commit: `main` at
  `62d4c544a65cb61110613cdc019b935659a17d26`
- development branch: `formal/easycrypt-computational-m1`
- draft pull request: `#1`
- frozen formal source commit in `blinding-pixels/Facets`:
  `7f685d35a72a463cbcc1052a81710bb02c0c5b80`

## Recovered exact sources

The frozen commit exposes the source files that were absent from the migrated
`formal/current-source` directory:

- `research/causal-dag-cgka/CausalDagCgka/Authorization.lean`
- `research/causal-dag-cgka/CausalDagCgka/Accountability.lean`
- the historical EasyCrypt game files under
  `research/causal-dag-cgka/easycrypt/`
- the historical EasyCrypt workflow.

The recovered Lean source hash for `Authorization.lean` is Git blob
`55b138aa423f46db69d50d4427d89d67636c6281`. The recovered
`Accountability.lean` blob is
`e85f9df0cb19943009a365597fa6350feffe7774`.

## Confirmed semantics used by the reference validator

1. Membership and capability grants are independent observed-remove sets.
2. Revocation tombstones exactly the grant tags visible in the signed causal
   context.
3. A capability-gated operation requires active membership and active capability
   for the exact principal.
4. Accepted operations are immutable evidence and unseen concurrent revocation
   does not retroactively remove an operation valid in the author's context.
5. A causally later operation that sees the sole capability tag revoked is
   rejected.
6. Fresh incarnation identity prevents inheritance of the old incarnation's
   capability tags.

## Production-policy mismatch found

The live `Facets` Rust repository currently projects owner/admin/member/viewer
roles and epoch authority. For example, `SpaceRole::may_issue_member_invites`
permits owner or admin. That is not yet the handoff's key-native,
observed-remove capability-fact protocol.

The computational game therefore cannot honestly claim source-to-production
identity today. The current reference model follows the handoff's protocol
semantics and records Rust correspondence as open. The final traceability table
must either:

- map these game operations to a concrete deployed key-native protocol API; or
- revise the handoff and prove the actual epoch/role protocol instead.

## Issuer policy selected for the reference checkpoint

To avoid an unconstrained `issuerAuthorized` Boolean, the executable reference
model uses this concrete recursive rule:

- genesis membership/capability facts form a creator-signed initialization
  chain: the first has empty context and each later fact names the exact prior
  initialization prefix;
- every later grant or revocation is signed by its issuer;
- the issuer must be an active principal with active `ADMIN` capability in the
  exact signed fact context;
- every context is an exact validated fact prefix in the reference execution;
- a retired incarnation can never be a membership-add target again.

This rule is a checkpoint decision, not yet a deployed-protocol fact. It must be
reviewed before the EasyCrypt reduction is promoted.

## Checker status

The branch workflow now runs the immutable EasyCrypt image
`ghcr.io/easycrypt/ec-test-box@sha256:84980006e8b01fe6497bbd0ecd67deeb5e7361d8ad17e27d24924122d368e0fc`
and preserves the exact checked source, hashes, checker output, and exit status
as a workflow artifact.

Verified progress on the pinned `r2026.07` checker:

- `AuthorizationState.ec` compiles;
- `CanonicalEncoding.ec` compiles;
- the repository anti-cheating audit passes with zero manifest axioms;
- deterministic projection/return normalization was committed at
  `e0d903c11b866a61d0bdbd647fcde2948e677ba2`;
- grouped EasyCrypt local declarations were split at
  `07ec408d320f184e6b73743a363945e1adc08337`;
- fixture-operator calls were converted to curried EasyCrypt application at
  `e2060de4d31641ad064f38a460de4d22e3eee4ab`;
- the complete dependency closure is not yet green, so no computational
  security theorem is marked complete.

## Next formal step

First obtain a completely green syntax/typecheck closure. Then structure
Deliverable A around the deterministic implication

```text
unauthorized acceptance
  => badOpSig \/ badFactSig \/ badHash \/ encodingFailure
```

Prove `encodingFailure` impossible from canonical encode/decode injectivity,
connect the signature events to concrete EUF-CMA reduction modules with
oracle-derived query losses, connect `badHash` to a collision adversary, and
finish with identical-until-bad plus the union bound. The authorization
lifecycle theorem shapes may be reused, but the EasyCrypt representation
mapping must be proved rather than imported. BeeKEM is outside Deliverable A.
