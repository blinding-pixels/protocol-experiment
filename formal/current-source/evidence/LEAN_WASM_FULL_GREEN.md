# Full Lean WASM green report

Date: 2026-08-27

## Result

The complete reconstructed combinatorial source closure passed a real Lean
WASM elaborator/kernel run:

- checker: Lean `4.33.0-pre`, `wasm32-unknown-emscripten`, commit
  `62b6a2291302d4bbeace37642a066b7510d0145c`;
- source components: 13;
- theorem declarations audited: 80;
- result: `hasErrors = false`;
- axiom-free theorems: 32;
- theorems using standard Lean axioms: 48;
- complete set of reported axioms: `propext`, `Quot.sound`;
- `sorry`, `admit`, declared `axiom`, `unsafe`, and `sorryAx`: absent;
- self-contained full-source SHA-256:
  `bdee462415deb6abed681e807f4f0d12cfa4472527c7fa4dc8b86d9a62ee6286`.

The raw kernel transcript is `LEAN_WASM_FULL_GREEN.log`. The reproducible
checker is `../../../verification/run-lean-wasm.sh`.

## Source provenance

The historical modules were restored from the repository's verified text
snapshot at `formal/historical-source-7f685d35/CausalDagCgka`. The current
`AuthorizationLifecycle.lean` and `Main.lean` were overlaid on that source.
All modules now live in `formal/current-source/CausalDagCgka`, so the active
package no longer depends on an implicit archive lookup for its imports.

## Exact boundary

This is substantive Lean kernel evidence for all theorem bodies in the source
closure. It is not yet an exact-toolchain package-build claim:

- the project pin is Lean `4.32.2`;
- this run used the pinned public Lean `4.33.0-pre` WASM fixture;
- the fixture emits exported-only `.olean` snapshots that omit private helper
  declarations used by the historical module layout, so the runner checks the
  deterministic complete source closure in one kernel invocation;
- an exact Lean 4.32.2 `lake build --wfail` remains required before claiming
  that the ordinary package build is green at the exact pin.

Lean does not mechanically discharge the EasyCrypt model. The correspondence
between these combinatorial invariants and the EasyCrypt games remains an
explicit model-fidelity obligation.
