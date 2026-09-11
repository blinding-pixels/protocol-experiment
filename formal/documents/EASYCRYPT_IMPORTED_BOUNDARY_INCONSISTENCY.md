## Current interface revision

The historical inconsistency described below is addressed by the oracle-only
contract and named opaque paper primitive in
`formal/documents/EASYCRYPT_IMPORTED_CONTRACT_REPAIR.md`. The original
reproducer and private-state bypasses now reject, but the complete supporting
proof closure is still unaccepted. Historical checker results below are not
new verification of the corrected source.

# Critical: the imported BeeKEM boundary derives false

Checked against production source `400591f6b2d7a5b331ad8a2c831dbbaef25e5f80` on
September 10, 2026. This finding supersedes any current security-completion
interpretation of the earlier top-level green checks. Historical CI records
remain historical records; their bytes and the imported axiom are unchanged.

The remote counter-proof checkpoint `f0d661fb98912fceede4f1f6f4b63f0a144362e2`
landed during this work. It changes only `BeeKemQueryCounterProofs.ec` and
`BeeKemCounterMutationProofs.ec`, neither of which belongs to the reproducer
foundation. It is integrated without rewriting either history; every production
`.ec` and `.eca` remains byte-identical to that newer remote source.

## What is established

The repository's current `beekem_theorem1_imported_normalized` axiom is
inconsistent with its own executable game and unrestricted module quantifiers.
A concrete instantiation satisfies every explicitly listed premise and makes
the conclusion false. The real pinned EasyCrypt checker accepts a derivation
of `false` from this axiom after independently accepting all local supporting
proof bodies.

This is **not** a claim to have broken the BeeKEM protocol or refuted the
published paper. The counterexample uses challenger-internal access which an
oracle-only cryptographic adversary is not meant to have. The EasyCrypt module
quantifier currently permits it. The failure is in the repository's formal
import/interface and thus in the basis on which its security claims are checked.

## Exact counterexample

`BoundaryDiagnosticInstance` satisfies `BEEKEM_PAPER_INSTANCE`. Its procedures
are direct aliases of the existing `BeeKemWitnessProtocol`,
`BeeKemInsecureNike`, `BeeKemInsecureNikeRandom`, and `BeeKemInsecureSe`
implementations. These deliberately insecure primitives are used only to
inhabit the interface and prove its correctness premises. They are not claimed
secure and do not replace a production reduction. In the minimal empty-user
case none of the protocol procedures are called at all.

`BoundaryHiddenBitReader(O : BEEKEM_KI_ORACLES)` satisfies the current adversary
module type, but its `attack` returns the existing
`BeeKemKiOracles(BeeKemProtocolOfPaperInstance(BoundaryDiagnosticInstance)).hidden_bit`.
It makes no oracle calls. The probability proofs run the actual `BeeKemKiGame`;
no challenger or sampling code is copied, bypassed or changed.

Both of these cases are checked without importing the security axiom:

- Empty users: the exact challenger samples a fair bit, initializes its oracle,
  and the reader returns that same bit. Success probability is one, safety
  probability is one, and both challenge and member-addition counters are zero.
- One initialized user: the same conclusions hold. The contradiction therefore
  does not depend on an empty-user input.

A separate `BoundaryConstantGuess` adversary, which makes no oracle calls and
returns false without reading challenger state, wins with probability one half
in the same minimal game. The hidden-bit read changes the result, rather than
a broken random-bit control or an unreachable test path.

For the nonempty counterexample, instantiate the axiom with:

```text
A = BoundaryHiddenBitReader
PaperInstance = BoundaryDiagnosticInstance
users = [beekem_witness_user]
kappa = 1
c = 0
n = 2
h = 1
group and membership = arbitrary parameters of the diagnostic
```

Every explicit premise is discharged:

```text
1 <= kappa
0 <= c
beekem_is_ceil_log2 2 1
Pr[NIKE symmetry game succeeds] = 1
for every message: Pr[SE correctness game succeeds] = 1
Pr[exact KI evidence is safe] = 1
Pr[challenge count <= 0 and addition count <= 2] = 1
```

The actual KI success probability is one, so the model's normalized advantage
is one half. The theorem multiplier is c * h = 0 * 1 = zero. Consequently the
RHS is zero for **every** pair of primitive reduction adversaries, regardless
of their advantages. Existential selection of those adversaries cannot repair
the inequality. No zero-valued probability or advantage operator was introduced.

`imported_boundary_contradiction` applies the unchanged axiom to precisely
those checked premises, eliminates the existential witnesses, and derives
one half <= zero, then `false`.

## Independent evidence and quarantine

The reproducer's foundation contains these 12 independently checked local files:

```text
BeeKemTypes.ec
BeeKemQueryLog.ec
BeeKemProtocol.ec
BeeKemSafety.ec
BeeKemKiGame.ec
BeeKemGameWitnesses.ec
BeeKemPrimitiveGames.ec
BeeKemPrimitiveContracts.ec
BeeKemPrimitiveWitnesses.ec
BeeKemConstruction.ec
BeeKemTheorem1Math.ec
BeeKemBoundaryCounterexample.ec
```

Their entire local dependency closure contains no local axiom declaration.
The isolated run then checks `BeeKemKiInterface.eca`, the only added local
axiom-bearing dependency, followed by `BeeKemBoundaryContradiction.ec`.
Every successful direct invocation exits zero and produces a nonempty `.eco`.
`BeeKemBoundaryNoAxiomSanity.ec` is separately rejected at `cannot prove goal
(strict)` without the disputed import. That rejection is not presented as a
proof of global consistency.

All inputs are copied into a fresh isolated directory containing only the
needed sources. No cached `.eco` is supplied initially. Each target's `.eco`
is removed before its direct check. The original computational sources are
unchanged by this diagnostic checkpoint. The installed checker and standard
libraries are those of the pinned image:

```text
ghcr.io/easycrypt/ec-test-box@sha256:84980006e8b01fe6497bbd0ecd67deeb5e7361d8ad17e27d24924122d368e0fc
```

The local run uses its verified exported filesystem under the original image's
charlie user (uid 1001), not a replacement checker. The previously recovered
compressed export has SHA-256:

```text
3ab255c31df19f1f9a4f1cf9bc957ff0eaf93c93720e8551bec992220df2a2e6
```

The contradiction theory is outside `computational/` and outside the public
proof import graph. No production theorem imports it. The 150-target public
closure remains unchanged. The new regression job belongs to the existing
vacuity workflow and treats acceptance of the contradiction as **failure**.
No previous mutation/diagnostic case is removed or weakened.

## Required repair boundary, not an assumption silently added

At minimum, the imported theorem needs an enforced oracle-private adversary
boundary: A must not directly read or write the challenger's hidden bit, private
protocol state, or logs, except through the supplied oracle procedures. The
existing procedure signature alone does not imply that property, as the checked
reader demonstrates. This is a module-access/modeling condition, not a new
cryptographic hardness assumption. Adding it changes the literal unrestricted
quantification and cannot be described as merely a successful tactic repair.

The same review must check primitive-module access and the scope of
`BEEKEM_PAPER_INSTANCE`: sharing one flat instance does not, by itself, encode a
refinement from arbitrary implementations of its callbacks to the paper's
specific construction. The current reproducer establishes the stated boundary's
inconsistency; it does not independently prove every possible construction-
binding defect or validate a replacement boundary.

Any replacement must be explicit, justified against the intended oracle model
and imported theorem, and propagated through the concrete reduction adversaries.
The public oracle operations, legitimate adversarial scheduling/reveal/
compromise capabilities, and required quantitative losses must be retained.
The false ancillary validator/control statements and the other direct proof
failures still require repair as well.

No new restriction, axiom, precondition, game change or security-bound change
has been applied to production here. The trusted interface has not been
silently narrowed. **The live-key phase remains blocked; further green importer
checks using this inconsistent boundary cannot establish the requested security
claim.**
