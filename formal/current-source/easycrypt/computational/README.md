# Computational proof development

Status: **Milestone 1 executable reference model committed; EasyCrypt proof kernel-pending**.

This directory is the new computational development required by
`formal/documents/EASYCRYPT_COMPUTATIONAL_PROOF_HANDOFF.md`.  The historical
EasyCrypt files remain historical evidence and are not imported here.

## Current checkpoint

Implemented now:

- key-native principals `(operationVerificationKey, incarnationNonce)`;
- explicit operation-envelope fields and canonical JSON test encoding;
- signed membership/capability grant and observed-remove revocation facts;
- deterministic authorization normalization;
- one executable validator performing all fourteen checks in the handoff;
- exact-incarnation authority and retired-incarnation non-revival;
- causal-view, authorization-digest, predecessor-closure, BeeKEM-update,
  history-grant, and puncture validation hooks;
- fourteen one-defense-removed Milestone 1 witnesses;
- canonical-encoding and visible-revocation negative controls;
- a lexical/mechanical audit tool under `tools/easycrypt/`.

Not yet claimed:

- no EasyCrypt reduction theorem has passed the pinned checker;
- `UnauthorizedReduction.ec` is not complete;
- live-key and content-key games have not begun;
- the four confidentiality-layer mutations—live/history separation, exposure
  exclusion, erasure, and public puncture—remain for later milestones;
- the Python signature implementation is test instrumentation, not a primitive
  security theorem;
- source-to-Rust canonical byte correspondence remains open.

## Run the current executable checkpoint

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

The signature is therefore part of node identity.  EasyCrypt and Rust must use
this rule consistently or revise it together before a final proof claim.

## Checker boundary

The required image remains:

```text
ghcr.io/easycrypt/ec-test-box:r2026.07
sha256:84980006e8b01fe6497bbd0ecd67deeb5e7361d8ad17e27d24924122d368e0fc
```

GitHub Actions produced no run for either push or pull-request events in the
canonical repository during this checkpoint.  No source in this directory may
be described as checker-accepted until a captured successful run over the exact
source hash exists.
