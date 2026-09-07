# Checked application/PRF control counterexamples

September 7, 2026. This is a diagnostic checkpoint, not completion of the live-key theorem.

## The statement defect

`LivePrfApplicationControls.ec` contains two unrestricted control claims:

- `application_prf_random_trace_reaches_every_oracle`
- `rejected_application_challenge_preserves_prf_routing`

Both assume only that the fourth argument, the primitive hidden bit, is false.
They conclude that the application reduction is eligible and wins. They do not
constrain the initial state, initial authorization facts, or retention parameter.

This is a genuine statement defect, not just a missing rewrite. The checked lemma
`application_prf_eligible_requires_valid_input` in
`LivePrfApplicationReduction.ec` derives, from the actual unrestricted reduction:

    eligible => initial_authorization <> None /\ 1 <= retention_kappa

It introduces no adversary or primitive-module restriction. Eligibility is not
an arbitrary adversary-supplied Boolean: the reduction calculates it from its
initial authorization, actual trace safety, and unauthorized-acceptance flag.

## Terminating counterexamples, not vacuous Hoare assertions

`LivePrfControls.ec` now directly proves both of these exact probability results,
for every initial memory `&m`:

    Pr[ApplicationPrfTraceGame.main_with_fixed_bit(
         live_witness_protocol_state, [], 0, false) @ &m :
         ! res.`mpge_eligible /\ ! res.`mpge_win] = 1%r

    Pr[ApplicationRejectedChallengeGame.main_with_fixed_bit(
         live_witness_protocol_state, [], 0, false) @ &m :
         ! res.`mpge_eligible /\ ! res.`mpge_win] = 1%r

Their underlying probability-one Hoare proofs symbolically execute the actual
control programs. Thus divergence cannot explain the counterexamples. The
inputs satisfy the original controls' sole precondition, but their outputs
contradict the original conclusions.

These results refute the unrestricted control statements. They are not an
attack on the live-key security claim at valid protocol parameters.

## Positive non-vacuity witness

The same executable `ApplicationPrfTraceGame`, with
`(live_witness_protocol_state, [], 1, false)`, now has a directly checked
probability-one theorem:

`initialized_application_prf_random_trace_reaches_every_oracle`

It proves eligibility, a winning false diagnostic guess, one real-only live
reveal, one sampled live challenge, one history query, and one constrained-history
query. The trace adversary's guess encodes that the reveal stayed real, the
challenge was sampled, and both history outputs returned. This is a new,
explicitly initialized witness, not a replacement for either unrestricted claim.
The deliberately insecure test primitives remain witness primitives only; no
security hop has been replaced by the test game.

## One executable definition and preserved public paths

The four original application-control module definitions were moved byte-for-byte
from `LivePrfApplicationControls.ec` to `LivePrfControls.ec`. The original public
module paths now contain direct EasyCrypt aliases to those definitions.
The programs and their oracle calls have not been changed or copied into a
second model. The aliases are definitional module identities, not assumed
simulation lemmas. This permits direct checking of the counterexamples without
importing the very claims they refute.

Both original unrestricted theorem statements and proof bodies remain in their
required direct-closure target. No precondition was strengthened, no failing
target was deleted or skipped, and neither original claim is reported repaired.
The dependency closure still contains exactly 150 unique targets.

## Checker and acceptance status

The checks use the unmodified EasyCrypt installation recovered from the CI
root filesystem exported from the pinned image:

    ghcr.io/easycrypt/ec-test-box@sha256:84980006e8b01fe6497bbd0ecd67deeb5e7361d8ad17e27d24924122d368e0fc

Inside that runtime, `opam exec -- easycrypt compile LivePrfControls.ec` returns
zero and produces a nonempty `.eco`. `LivePrfIdealControls.ec` and
`ComputationalProof.ec` also compile directly, and `audit_computational.py`
passes. These are focused checks, not acceptance of the full dependency closure.

The unchanged unrestricted application-control target remains unaccepted.
A local 20-second diagnostic invocation timed out while working through its
original proof. That timeout is not the evidence of falsity: the completed,
probability-one counterexamples above are.

No new axiom or unproved premise has been added. The final security theorem must
not be called complete while the direct closure is red. In particular, a green
public entry that imports these unchecked statements is not a proof that their
bodies are valid.
