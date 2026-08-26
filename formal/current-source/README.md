# Current Lean source

This package copies the last historical kernel-checked combinatorial source and
adds `CausalDagCgka.AuthorizationLifecycle` for the newly exposed removal/rejoin
boundary.

Pinned toolchain: Lean `4.32.2`.

Current status:

- lifecycle theorem status is **kernel-pending**;
- source authored without `sorry`, `admit`, or `sorryAx`;
- executable finite oracle and negative controls pass;
- exact Lean 4.32.2 kernel run is pending because this execution environment
  could not retrieve the 564 MB official release asset and CI is intentionally
  disabled.

The new theorems must not be described as kernel-checked until `lake build
--wfail` and the existing axiom audit run successfully on this exact tree.
