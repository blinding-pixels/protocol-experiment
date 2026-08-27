# Current Lean source

This package restores the complete historical combinatorial source and adds
`CausalDagCgka.AuthorizationLifecycle` for the newly exposed removal/rejoin
boundary.

Pinned toolchain: Lean `4.32.2`.

Current verification status:

- the complete 13-module, 80-theorem source closure passes the real Lean WASM
  4.33.0-pre elaborator and kernel;
- all 80 theorems have explicit `#print axioms` evidence: 32 are axiom-free and
  48 use only `propext` and `Quot.sound`;
- no `sorry`, `admit`, declared `axiom`, `unsafe`, or `sorryAx` is present;
- `verification/run-lean-wasm.sh` reproduces the full closure and axiom audit;
- the exact pinned Lean 4.32.2 `lake build --wfail` remains pending.

The WASM result is valid kernel evidence for the source closure, but it must not
be described as an exact-toolchain package build. See
`evidence/LEAN_WASM_FULL_GREEN.md` for the result and remaining boundary.
