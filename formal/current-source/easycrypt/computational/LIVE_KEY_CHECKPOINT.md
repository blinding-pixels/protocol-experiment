# Deliverable L live-key checkpoint

Exact branch: `formal/easycrypt-live-key-reduction`

This checkpoint records the active, non-release Deliverable L state.

- Deliverable A remains the previously checker-accepted authorization reduction.
- `LiveKeyGame.ec` contains the executable adaptive live-key trace scaffold.
- `LiveKeyWitnesses.ec` contains the initial honest/admissibility controls.
- `LiveAuthenticationReduction.ec` connects the shared live execution to Deliverable A's exact origin-aware bad event and named primitive games.
- The live closure reuses the single `PG` clone exported by `UnauthorizedSignatureReduction`; it does not create nominally distinct copies of the Deliverable A signature or collision games.
- The live construction is reduced to Deliverable A's exact one-procedure adversary interface before it is supplied to the existing A0--A5 reduction functors.
- BeeKEM challenge embedding, the multi-domain PRF reduction, ideal-game independence, the final Deliverable L bound, and the remaining live mutation controls are still open.

A green run for this checkpoint means only that the active source closure, anti-cheating audit, executable reference tests, and current EasyCrypt entry point pass under the pinned checker. It is not a claim that Deliverable L is complete.
