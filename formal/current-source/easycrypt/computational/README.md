# Computational proof development

Status: **first concrete Milestone 1 non-vacuity theorem checker-accepted; the final unauthorized-acceptance reduction remains open**.

This directory is the new computational development required by
`formal/documents/EASYCRYPT_COMPUTATIONAL_PROOF_HANDOFF.md`. The historical
EasyCrypt files remain historical evidence and are not imported here.

## Checker-accepted checkpoint

The pinned EasyCrypt `r2026.07` kernel now accepts the following direct theorem
through the public production validator:

```text
lemma witness_honest_operation_accepted &m :
  Pr[
    ValidateOperation(TestSignature).validate(
      Production,
      witness_honest_edit_operation,
      witness_base_view_exact,
      witness_base_state_exact
    ) @ &m :
    res.`vr_accepted
  ] = 1%r.
```

This is a concrete semantic theorem, not an imported success premise. The proof:

- decodes and canonically re-encodes the exact signed operation;
- checks the protocol domain/version, document binding, freshness, predecessor
  existence, and exact causal closure;
- normalizes the seven signed authorization facts inside the validator;
- checks the resulting authorization digest;
- checks signature bytes and author-key binding using the current idealized
  `TestSignature` implementation;
- proves exact-incarnation membership and `CapEdit` authority;
- validates the operation body and all kind-specific production branches;
- separately proves validator losslessness with a decreasing
  `size remaining` loop variant;
- combines semantic correctness and termination to obtain probability one.

The same checker entry point also exposes the negative control
`noncanonical_rejection_probability_one`, which proves that a concrete
noncanonical operation is rejected by the same public validator with the exact
`FailureCanonicalReencoding` result and probability one.

The checked entry point is `ComputationalProof.ec`. At commit
`e2d9565c83bc40a5bd30809653fb497fd9bb93c7`:

- the Milestone 1 workflow passed its anti-cheating audit and compiled
  `HonestOperationContract.ec`;
- the full computational workflow passed its source audit and compiled
  `ComputationalProof.ec`;
- the checkpoint audit reported **25 EasyCrypt sources and 0 manifest axioms**;
- both checker and audit exit statuses were zero;
- the full evidence artifact digest was
  `sha256:f2c8bf1baadf3c2fb45078bbed053cd93177ad9e2ae9d0a745c97561e8dac7f2`.

Checker runs:

- `https://github.com/blinding-pixels/protocol-experiment/actions/runs/33146735736`
- `https://github.com/blinding-pixels/protocol-experiment/actions/runs/33146735749`

## Implemented model surface

Implemented now:

- key-native principals `(operationVerificationKey, incarnationNonce)`;
- explicit operation-envelope fields and canonical test encoding;
- signed membership/capability grant and observed-remove revocation facts;
- deterministic authorization normalization;
- one executable validator performing the fourteen checks in the handoff;
- exact-incarnation authority and retired-incarnation non-revival;
- causal-view, authorization-digest, predecessor-closure, BeeKEM-update,
  history-grant, and puncture validation hooks;
- fourteen one-defense-removed Milestone 1 witnesses;
- canonical-encoding and visible-revocation negative controls;
- a comment/string-aware mechanical audit under `tools/easycrypt/`.

## Explicit non-claims

This checkpoint does **not** yet establish the handoff's final Deliverable A
advantage bound. In particular:

- `UnauthorizedReduction.ec` and the A0-to-A5 reduction chain are not complete;
- no EUF-CMA or collision-resistance reduction has yet been imported or
  instantiated;
- `TestSignature` is idealized executable proof instrumentation, not a
  cryptographic signature-security theorem;
- live-key and content-key games and reductions have not begun;
- the four confidentiality-layer mutations—live/history separation, exposure
  exclusion, erasure, and public puncture—remain for later milestones;
- source-to-Rust canonical-byte correspondence remains open;
- abstract erasure does not prove concrete Rust, persistence, crash-recovery,
  or operating-system residue behavior.

The result therefore closes the first required anti-vacuity obligation: an
honest canonical operation really can traverse the modeled production validator
and be accepted. It is not yet the theorem that unauthorized acceptance has
only the final primitive-security advantage bound.

## Run the executable and mechanical checks

From the repository root:

```text
python -m unittest discover \
  -s formal/current-source/easycrypt/computational \
  -p 'test_*.py' -v

python tools/easycrypt/audit_computational.py
```

The reference suite contains eighteen tests: four positive/baseline controls and
fourteen one-defense-removed authorization witnesses.

## Node identity choice

This development chooses:

```text
nodeId = SHA-256(canonicalOperationWire || 0x00 || canonicalSignature)
```

The signature is therefore part of node identity. EasyCrypt and Rust must use
this rule consistently or revise it together before a final proof claim.

## Checker boundary

The required immutable checker remains:

```text
ghcr.io/easycrypt/ec-test-box:r2026.07
sha256:84980006e8b01fe6497bbd0ecd67deeb5e7361d8ad17e27d24924122d368e0fc
```

A claim is checker-accepted only when a successful run identifies the exact
source commit, source hashes, immutable image digest, audit output, and checker
exit status. Later source changes require new successful evidence.
