# Checkpoint — 2026-08-25

Remote checkpoint parent: `835083accb3a357c960ff651e1055f64f2bd0302`  
Local standalone checkpoint: `3b69b96` (`docs: checkpoint 77-test lifecycle status`)

## Preserved

- dedicated repository: `blinding-pixels/protocol-experiment`;
- CI remains off; no workflow files were added;
- verified twelve-part text-source snapshot with archive and per-part hashes;
- machine-readable assumption register;
- formal claim-status matrix;
- exact 77-test local report;
- updated formal assumption revalidation;
- current Lean authorization-lifecycle source pinned to Lean 4.32.2;
- deployment, operational-fidelity, trust/consistency, timing, BeeKEM, and formal-package boundary documents.

## Current formal verdict

The abstract conditional protocol spine still holds under its stated cryptographic,
erasure, and delivery assumptions. One stronger lifecycle claim is false:
membership removal alone does not prevent a surviving capability from reviving
when the same identity is re-added.

Two no-new-cryptography repairs are modeled:

1. coupled tombstoning of every visible capability tag during an
   authority-revoking removal;
2. incarnation-scoped member identities, so rejoin creates a fresh identity.

The current Lean lifecycle source formalizes the counterexample and both repairs,
but remains **kernel-pending** until the exact Lean 4.32.2 build and existing
axiom audit run on that source.

## Still open

- finish publishing the remaining formal documents as browsable files;
- import the complete frozen Rust and proof tree as live source rather than only
  through the verified snapshot;
- compile and execute all correct and exactly one-defense-removed variants;
- compare the compiled Rust canonical-state vector byte-for-byte with the
  independent oracle;
- populate the full proof-to-source-to-binary evidence graph;
- run production lifecycle/persistence fault-injection checks;
- generate fresh timing, cache, and assembly evidence for each exact target;
- obtain exact Lean 4.32.2 kernel acceptance for the new lifecycle module.

No new cryptographic primitive, ratchet, or protocol layer has been added.
