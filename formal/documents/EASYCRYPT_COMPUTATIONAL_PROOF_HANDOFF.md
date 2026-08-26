# EasyCrypt computational proof handoff

## Status and purpose

This document is the implementation specification for the missing computational
security proof. It is intentionally stricter than the current EasyCrypt files.

The existing files establish probability arithmetic, event inclusions, and toy
reachability examples. They are useful as a proof outline but are not a
faithful computational proof of the protocol. Do not extend them by adding
more arbitrary `RootSource`, `KDF`, or `extra_checks` modules. Start the
computational development described here in a new directory and retain the old
files only as historical evidence.

The proof has three independent deliverables:

1. resistance to unauthorized operation acceptance;
2. indistinguishability of a live application key;
3. indistinguishability of an ungranted content key after the stated erasure
   frontier.

Each deliverable needs its own real game, ideal game, reductions, query bounds,
mutation witnesses, and final theorem. A single triangle-inequality lemma is
not a substitute for any of them.

## Threat model fixed by this handoff

The target theorem inherits BeeKEM's exact security boundary:

- honest execution of BeeKEM by protocol participants;
- authenticated causal broadcast;
- adversarial delivery scheduling and network partitions within ACB;
- adaptive reveal, challenge, and snapshot-compromise queries;
- finite `kappa >= 1` and the paper's exact `bee-safe_kappa` predicate.

The authorization layer additionally permits an adversary to submit arbitrary
public operations, signatures, grants, revocations, history capabilities, and
malformed encodings. These inputs are accepted only through the validator
defined below.

A genuinely authorized principal that deliberately performs a harmful but
well-formed operation is outside the unauthorized-acceptance win condition.
The theorem does not claim Byzantine security against such a principal.

The proof concerns protocol semantics and cryptographic messages. Rust
serialization, zeroization, persistence, crash recovery, and OS residue belong
to the Rust crate. The computational model must state the abstract erasure and
canonical-encoding contracts on which it relies, but must not pretend to prove
their concrete implementation.

## Required simplification before writing games

Use a key-native incarnation as the cryptographic principal:

```text
Principal = (operationVerificationKey, incarnationNonce)
```

The operation signature therefore authenticates the cryptographic principal
without a separate identity-to-key credential. A stable human account may map
to several incarnations at the application layer, but it is not the security
identity used by these games.

Membership and capability grants are signed public facts. Do not introduce a
second opaque role-credential primitive unless the deployed protocol actually
uses one. If an external identity or role credential is later required, add a
separate concrete soundness game and reduction; never represent it by an
unconstrained Boolean `verify` result.

Every rejoin uses a fresh incarnation nonce. A retired incarnation is never a
valid add target again.

## Canonical protocol objects

The EasyCrypt model must represent the following fields explicitly. A comment
saying that a generic `context` or `message` contains them is insufficient.

```text
OperationEnvelope = {
  protocolDomain,
  protocolVersion,
  documentId,
  operationId,
  author : Principal,
  requiredCapability,
  directPredecessors : CanonicalSet<NodeId>,
  authorizationDigest,
  operationKind,
  operationBody,
  nonce
}

SignedOperation = {
  envelope : OperationEnvelope,
  signature
}
```

The canonical transcript is:

```text
opTranscript(op) =
  Encode(
    "protocol-operation",
    protocolVersion,
    documentId,
    operationId,
    author.verificationKey,
    author.incarnationNonce,
    requiredCapability,
    sortedUnique(directPredecessors),
    authorizationDigest,
    operationKind,
    operationBody,
    nonce)
```

The node identifier is the collision-resistant hash of this complete canonical
transcript plus the signature when the DAG format makes the signature part of
the node identity. Pick one rule and use it consistently.

The model must separately represent:

```text
MembershipGrant(principal, tag, issuer, context)
MembershipRevoke(observedTags, issuer, context)
CapabilityGrant(principal, capability, tag, issuer, context)
CapabilityRevoke(observedTags, issuer, context)
HistoryGrant(issuer, recipient, mergeNode, region, cover, context)
Puncture(issuer, region, context)
AcceptedOperation(operationId, author, capability, context, transcript)
```

Public authorization state is obtained only from signature-valid, context-valid
facts and normalized with the observed-remove semantics already proved in
Lean. Secret BeeKEM state, segment roots, subtree seeds, signing keys, and
derived content keys never enter the public join.

## Exact validator modeled by the games

Define one executable EasyCrypt procedure `ValidateOperation`. It accepts a
signed operation and a causally closed public view. It must perform all of the
following checks itself:

1. canonical decoding succeeds and re-encoding is byte-identical;
2. protocol domain and version match;
3. document ID matches the target document;
4. operation ID and nonce satisfy the freshness rule;
5. every direct predecessor exists and the supplied view is its exact causal
   closure;
6. `authorizationDigest` equals the normalized authorization state computed
   from that closure;
7. the author signature verifies over `opTranscript(op)` under the verification
   key inside `op.author`;
8. the author incarnation is active in that state;
9. the required capability is active for that exact incarnation;
10. the operation body is valid for its kind;
11. an add target is fresh and not retired;
12. a BeeKEM update is authored for the author's own active incarnation and
    its path is valid for the exact predecessor tree;
13. a retrospective grant binds issuer, recipient, merge node, exact region,
    segment-tagged cover, causal context, and protocol version;
14. a puncture binds the canonical region and the puncture capability.

There must be no parameterless `ProtocolGate.accept()` and no unconstrained
`extra_checks` predicate. The validator receives the exact operation and state
that determine its result.

## Shared adaptive oracle environment

Build one stateful oracle environment used by the three games. At minimum it
must expose:

```text
CreateGroup(creator, initialMembers)
Deliver(controlMessage, recipient)
SendBeeKemUpdate(member)
AddMember(author, freshPrincipal, leafKey)
RemoveMember(author, targetPrincipal)
GrantCapability(author, targetPrincipal, capability)
RevokeCapability(author, observedGrantTags)
SubmitOperation(signedOperation)
IssueHistoryGrant(author, recipient, mergeNode, region)
PublishPuncture(author, region)
RevealLiveKey(node)
RevealContentKey(segment, index)
RevealHistoryCapability(grant)
CompromiseProtocolState(principal)
ChallengeLive(node)
ChallengeContent(segment, index)
```

The environment maintains:

- the BeeKEM per-member states and operation graph required by the paper game;
- the authenticated public fact set and exact causal closures;
- active and retired incarnations;
- accepted-operation evidence;
- segment/checkpoint metadata;
- issued history capabilities;
- public punctures;
- retained BeeKEM secrets bounded by `kappa`;
- retained history-export state bounded by `rho`;
- an append-only query log used by all safety predicates;
- challenge and reveal bookkeeping.

The adversary controls oracle scheduling and all untrusted bytes. The game, not
the adversary, computes validation, causal closure, exposure, and admissibility.

## Imported premises: exact allowlist

Imported assumptions must live in one abstract-theory file,
`ImportedSecurity.eca`, and be listed in a machine-readable assumption
manifest. No other proof file may declare `axiom`.

The allowlist is:

1. **BeeKEM Theorem 1.** The exact KI-DCGKA game, `bee-safe_kappa`, query
   restrictions, and bound

   ```text
   c * ceil(log2(n)) *
     (Adv_NIKE_HKR_CKS(B) + Adv_SE_MU_CPA(C))
   ```

   for `kappa >= 1`.

2. **Operation signature security.** EUF-CMA, or strong EUF-CMA if the protocol
   relies on signature uniqueness rather than only unforgeability.

3. **Canonical transcript hashing.** Collision resistance. Canonical encoding
   injectivity should be proved as a deterministic lemma, not assumed as hash
   security.

4. **Multi-domain key schedule.** A selective or adaptive PRF game in which the
   adversary may receive every authorized constrained history output while the
   challenged live or history domain output remains pseudorandom. Ordinary
   single-output PRF security is not sufficient unless a reduction derives the
   required leakage statement.

5. **Constrained segment tree.** A constrained-PRF or PRG-tree game permitting
   adaptive disclosure of subtree seeds that do not cover the challenge leaf.

6. **Grant transport.** The exact KEM security and AEAD confidentiality and
   integrity games used by the concrete transport construction.

7. **Abstract erasure contract.** Once an honest state crosses a modeled
   deletion frontier, erased secrets are absent from later
   `CompromiseProtocolState` responses. This is a trace-model condition, not a
   cryptographic theorem about Rust or the operating system.

BeeKEM's imported axiom must be stated only over BeeKEM's own KI-DCGKA game. It
must not mention `ProtocolReal`, `LiveReal`, `ContentReal`, our authorization
gate, or one of our adjacent game differences. Applying the premise requires a
concrete reduction module from our adversary to a BeeKEM adversary.

An imported primitive advantage must always be the probability of a named
primitive game run with a named reduction adversary. Do not declare arbitrary
real-valued operators such as `signature_adv`, `prf_adv`, or `tree_loss` and
then use them without connecting them to those games.

## Deliverable A: unauthorized-operation acceptance

### Real game

`UnauthorizedReal(A)` runs the shared environment and lets `A` adaptively
submit operations and manipulate all public protocol inputs. It wins when an
operation is accepted even though, in the exact signed causal context named by
that operation, at least one of these statements is false:

```text
author incarnation is active
required capability is active for that incarnation
operation transcript is the transcript that was signed
operation body satisfies its kind-specific policy
```

A harmful operation by a principal that genuinely has the required capability
is not an unauthorized win.

### Required hops and reductions

- **A0 - real validator.** Execute the validator exactly as specified.
- **A1 - canonical transcript.** Set `badHash` when distinct complete
  transcripts yield the same digest. Construct `BHash(A)` that outputs the two
  transcripts as a collision.
- **A2 - signature origin.** Set `badSig` when an accepted signature/transcript
  pair was not returned by the signing oracle for that author key. Construct
  `BSig(A)` for the selected signature game, including the exact multi-user
  guessing loss.
- **A3 - signed authorization facts.** Show that every active membership and
  capability tag in the accepted context either descends from genesis through
  policy-valid signed issuers or gives `BSigFacts(A)` a signature forgery. This
  must cover grants and revocations, not only the final operation signature.
- **A4 - exact causal state.** Prove that, absent decoding/hash/signature bad
  events, the causal closure and normalized authorization digest used by the
  validator equal the mathematical observed-remove state. Reuse or transcribe
  the Lean theorem with a source hash and prove the representation mapping.
- **A5 - ideal authorization.** Acceptance of an unauthorized operation is
  impossible by evaluation of `ValidateOperation`; prove probability zero.

### Required theorem shape

```text
AdvUnauthorized(A)
 <= qOpSig * AdvEUFCMA(BSig(A))
  + qFactSig * AdvEUFCMA(BSigFacts(A))
  + AdvCollision(BHash(A))
  + encodingFailure(A)
```

`encodingFailure(A)` must be zero after canonical encoding injectivity is
proved, or be replaced by a named concrete primitive game. No unexplained
`negl(lambda)` term is allowed.

## Deliverable L: live application-key indistinguishability

### Real game

The game samples a hidden bit `b`. `A` receives the full shared oracle
environment. For an admissible `ChallengeLive(v)` query:

```text
S_v = BeeKEM internal group secret at v
L_v = F(S_v,
        "live" || protocolVersion || documentId || nodeId(v)
        || authorizationDigest(v))

return L_v       when b = 1
return uniform   when b = 0
```

The raw `S_v` is never returned by the application protocol. The adversary may
receive every history capability and history-derived output permitted by the
query log. The challenge is admitted only when the corresponding BeeKEM query
trace satisfies the paper's exact `bee-safe_kappa` predicate.

The advantage is normalized explicitly, for example:

```text
AdvLive(A) = abs(Pr[guess = b] - 1/2)
```

Do not use `Pr[A.guess(actualKey)]` as the security definition.

### Required hops and reductions

- **L0 - real protocol.** Full validator, BeeKEM, key schedule, history
  disclosures, compromise responses, and challenge bit.
- **L1 - authenticated public transcript.** Abort on the exact bad events from
  Deliverable A. Reuse its reductions rather than assuming an `authenticated`
  Boolean.
- **L2 - BeeKEM challenge embedding.** Construct `BBeeLive(A)` implementing
  BeeKEM's complete KI-DCGKA adversary interface. It must translate create,
  add/remove, update, deliver, reveal, challenge, and compromise queries and
  prove that an accepted live challenge yields a `bee-safe_kappa` BeeKEM
  challenge. Replace `S_v` by BeeKEM's real-or-random test value.
- **L3 - multi-domain PRF.** Construct `BPRFLive(A)`. It must answer every
  permitted history-domain query and constrained capability disclosure while
  embedding its challenge in the live domain and binding every domain label to
  the complete transcript.
- **L4 - ideal challenge.** Prove the challenge is independent of `b`, hence
  the normalized advantage is zero.

### Required theorem shape

```text
AdvLive(A)
 <= c * ceil(log2(n)) *
      (AdvNIKE_HKR_CKS(BNike(BBeeLive(A)))
       + AdvSE_MU_CPA(BSe(BBeeLive(A))))
  + AdvMDPRF(BPRFLive(A))
  + AuthLoss(A)
```

`AuthLoss(A)` must expand to the named reductions from Deliverable A. Every
query factor must be derived from the oracle code and recorded in the theorem.

## Deliverable C: ungranted content-key indistinguishability

### Exposure and admissibility

For a content challenge `(segment s, index i)` at node `v`, compute inside the
game:

```text
X_(kappa,rho,Gamma)(v)
  = E_kappa(v)
    union H_rho(v)
    union Granted_Gamma(v)
```

Reject the challenge unless all are true:

- `(s,i)` is outside `X_(kappa,rho,Gamma)(v)`;
- the content key was not explicitly revealed;
- no corrupted recipient received a capability covering `(s,i)`;
- no retained subtree seed or segment root covers `(s,i)`;
- every honest state formerly covering `(s,i)` crossed the modeled deletion
  frontier;
- the opening BeeKEM node satisfies `bee-safe_kappa`;
- the index is not made trivially readable by the public policy selected for
  the challenge.

The exposure predicate must be executable game state derived from the oracle
log. It may not be an unconstrained Boolean supplied by the adversary.

### Real challenge

```text
R_s = F(S_v,
        "history" || protocolVersion || documentId || segmentId(s)
        || authorizationDigest(v))
D_(s,i) = TreeEval(R_s, segmentId(s), i)

return D_(s,i)   when b = 1
return uniform   when b = 0
```

### Required hops and reductions

- **C0 - real protocol.** Execute the complete shared environment.
- **C1 - authenticated transcript.** Reuse Deliverable A for operation, grant,
  region, recipient, merge-node, segment, and puncture binding.
- **C2 - BeeKEM embedding.** Construct `BBeeContent(A)` and prove the selected
  opening node produces an admissible BeeKEM challenge.
- **C3 - history-domain PRF.** Construct `BPRFHistory(A)` that replaces `R_s`
  while simulating all permitted live-domain outputs and other segment roots.
- **C4 - constrained-tree path hybrid.** Use the exact-cover theorem to find
  the first unrevealed edge on the root-to-`i` path. Construct one PRG or
  constrained-PRF adversary per hybrid, or a random-index reduction with the
  explicit depth loss. Prove that no disclosed subtree capability is an
  ancestor of `i`.
- **C5 - grant transport.** If transport ciphertexts appear in the adversary's
  view, construct the KEM and AEAD reductions needed to replace protected
  payloads. Prove both confidentiality and ciphertext integrity where forged
  grants affect protocol state.
- **C6 - ideal challenge.** Prove normalized advantage zero.

### Required theorem shape

```text
AdvContent(A)
 <= BeeKemLoss(BBeeContent(A))
  + AdvMDPRF(BPRFHistory(A))
  + depth * AdvPRG(BTree(A))
  + qKem * AdvKEM(BKem(A))
  + qAeadConf * AdvAEADConf(BAeadConf(A))
  + qAeadInt * AdvAEADInt(BAeadInt(A))
  + AuthLoss(A)
```

Expand `BeeKemLoss` to Theorem 1 in the final corollary. Terms that do not occur
in the concrete protocol must be removed rather than retained decoratively.

## Required EasyCrypt file layout

```text
formal/current-source/easycrypt/computational/
  ProtocolTypes.ec
  CanonicalEncoding.ec
  AuthorizationState.ec
  ProtocolOracles.ec
  ImportedSecurity.eca
  BeeKemKiInterface.eca
  PrimitiveGames.eca
  UnauthorizedGame.ec
  UnauthorizedReduction.ec
  LiveKeyGame.ec
  LiveKeyReduction.ec
  ContentKeyGame.ec
  ContentKeyReduction.ec
  MutationWitnesses.ec
  Main.ec
  ASSUMPTION_MANIFEST.json
  README.md
```

`Main.ec` imports the three final reductions and prints only final public
theorems. Intermediate game files may print local lemmas during development but
must not be mistaken for final security statements.

## Anti-cheating rules

These rules are release blockers.

1. No `admit`, `abort`, `sorry`, `by admit`, disabled proof block, or equivalent
   placeholder anywhere in the dependency closure.
2. No `axiom` outside `ImportedSecurity.eca`, `BeeKemKiInterface.eca`, and the
   standard EasyCrypt libraries.
3. Every allowed imported axiom is enumerated by exact declaration name and
   source theorem in `ASSUMPTION_MANIFEST.json`.
4. No imported axiom or lemma premise may mention one of our real/ideal games,
   our final advantage, or the adjacent probability difference it is supposed
   to prove.
5. In particular, premises shaped like the following are forbidden:

   ```text
   h : abs(Pr[OurGame0] - Pr[OurGame1]) <= primitiveBound
   ```

   The proof must construct the primitive adversary and derive that inequality
   from the primitive game.
6. No arbitrary real-valued `Adv`, `loss`, or `negl` operator on a final RHS.
   Every term is the probability of a named game with a named reduction
   adversary, or a proved zero.
7. No parameterless security gate and no unconstrained Boolean standing for
   signatures, authorization, causal closure, exposure, erasure, or challenge
   admissibility.
8. No proof whose only substantive step is `abs_triangle2`, `abs_triangle3`,
   `mu_sub`, `smt`, or `ring`. Those lemmas may combine previously proved
   reductions but are not reductions themselves.
9. No defining the desired bad event as `primitiveBad /\ extraChecks` and then
   presenting `Pr[primitiveBad /\ extraChecks] <= Pr[primitiveBad]` as the
   security reduction.
10. No identity real/ideal hop, unreachable game branch, constant-false win
    event, empty adversary interface, or challenge that is never issued.
11. No toy-only non-vacuity result. Witnesses must instantiate the same game and
    validator used by the final theorem.
12. No source-level claim of checker acceptance without a captured successful
    run from the pinned EasyCrypt image over the exact source hash.

## Anti-triviality and mutation requirements

The test suite must include one matrix of one-defense-removed variants. Each
row removes exactly one production validation or domain-binding condition. For
every row, provide an adversary accepted by the mutated game that wins with
probability one or with an explicitly derived non-negligible probability.

Required rows:

| Removed defense | Required witness |
| --- | --- |
| operation signature | forge an operation as another principal |
| author-key binding | relabel a valid signature to another author |
| incarnation binding | reuse an old incarnation's authority after rejoin |
| document binding | replay an operation across documents |
| protocol version/domain | replay across protocol versions or message types |
| operation body binding | change the body under a valid authorization proof |
| required-capability binding | substitute a stronger capability |
| exact causal-context binding | replay a pre-revocation authorization |
| authorization digest binding | supply a context with a different active set |
| predecessor completeness | omit a causally prior revocation |
| grant recipient binding | redirect a retrospective grant |
| merge-node binding | reuse a grant at another merge |
| region digest binding | enlarge a retrospective region |
| segment tag | reinterpret a subtree seed in another segment |
| live/history domain separation | use a history disclosure to test a live key |
| challenge exposure exclusion | challenge a previously granted leaf |
| erasure premise | compromise a retained covering secret after deletion |
| public puncture check | read a publicly punctured index |

The unmutated game must have an honest end-to-end witness reaching each
challenge and acceptance path. A mutation test that only proves a buggy helper
returns `true` is insufficient; it must win the corresponding real security
game.

Also require these semantic controls:

- instantiate an intentionally insecure signature scheme and demonstrate that
  the signature reduction advantage becomes one;
- instantiate an intentionally non-pseudorandom KDF and demonstrate a live-key
  distinguisher;
- instantiate a tree that leaks every leaf from one capability and demonstrate
  a content-key distinguisher;
- show the final ideal live and content games have advantage exactly zero;
- show at least one admissible and one inadmissible challenge trace for every
  clause of `bee-safe_kappa` and `X_(kappa,rho,Gamma)`;
- show that every reduction actually invokes its primitive challenge oracle;
- fail the audit if deleting a reduction module leaves the final theorem
  unchanged.

## Faithfulness obligations

Checker acceptance proves the games as written. It does not prove that they are
the correct games. Before the result is promoted, an independent reviewer must
approve a traceability table containing:

```text
protocol operation/spec clause
  -> EasyCrypt procedure and state fields
  -> Rust crate API responsible for enforcement
  -> positive execution witness
  -> one-defense-removed witness
```

The table must cover every validator rule, oracle, challenge restriction,
exposure component, erasure transition, and domain label.

The BeeKEM wrapper receives a separate line-by-line review against Figures 3,
8, and 9 and Appendix B of ePrint 2026/1434. Its query translation must preserve
the complete query log used by `bee-safe_kappa`.

The canonical encoder receives cross-language test vectors in the Rust crate.
EasyCrypt may assume the deterministic encoding function used by its game, but
the source-to-model correspondence remains open until Rust produces the same
bytes.

## Mechanical audit and checker evidence

Pin EasyCrypt by immutable container digest, not only by tag. The image pulled
for this handoff is:

```text
ghcr.io/easycrypt/ec-test-box:r2026.07
sha256:84980006e8b01fe6497bbd0ecd67deeb5e7361d8ad17e27d24924122d368e0fc
```

Record the resolved digest before accepting evidence. Run every `.ec` and
`.eca` dependency in a fresh container and preserve:

- image tag and digest;
- EasyCrypt version output;
- Why3 and solver versions;
- exact source-tree hash;
- command line;
- stdout, stderr, and exit status;
- dependency closure;
- assumption-manifest validation;
- placeholder and forbidden-premise audit;
- theorem names printed by `Main.ec`.

The audit must parse code rather than rely only on grep so that forbidden terms
inside comments are ignored and proof blocks hidden through preprocessing are
included. Grep remains a useful independent check:

```text
rg -n -i '\b(axiom|admit|abort|sorry)\b' computational
```

The expected nonzero list is exactly the allowlisted imported declarations in
the two abstract-theory files.

## Milestones and stop conditions

### Milestone 1 - authorization only

Finish Deliverable A before live or content confidentiality. Stop if the
protocol does not yet have a concrete principal, grant issuer, canonical
transcript, or capability delegation policy; those decisions cannot be hidden
inside abstract Booleans.

### Milestone 2 - live key

Finish the BeeKEM oracle wrapper and live multi-domain PRF reduction. Stop if
the wrapper cannot prove that every accepted challenge is `bee-safe_kappa`, or
if a permitted history disclosure provides a checkable relation to the live
challenge.

### Milestone 3 - content key

Finish the exposure predicate, constrained-tree reduction, and transport
reductions. Stop if future history-grant capability requires retaining a seed
that covers the proposed challenge; the challenge is then inadmissible rather
than secure.

### Milestone 4 - combined corollary

Only after A, L, and C independently pass may `Main.ec` state the combined
conditional theorem and substitute BeeKEM Theorem 1's concrete NIKE/SE bound.

## Definition of done

The computational proof is complete only when all of the following hold:

- the three real games execute the actual validator and shared oracle state;
- the three ideal games have proved zero normalized advantage;
- every adjacent hop has a concrete reduction adversary or a proved exact
  equivalence;
- every primitive term names a game and reduction adversary;
- every query loss is explicit and derived;
- the BeeKEM premise is applied only through a faithful KI-DCGKA wrapper;
- no forbidden placeholder or conclusion-shaped assumption exists;
- every mandatory mutation has a winning witness in the real game;
- the exact dependency closure passes the real pinned EasyCrypt checker;
- the checker evidence and source hashes are committed;
- an independent cryptographer signs off on the game/spec faithfulness table;
- documentation calls the result conditional on BeeKEM, primitive security,
  modeled erasure, honest BeeKEM execution, and ACB.

Until then, call the work a computational proof skeleton.

## Assumption revalidation

This handoff deliberately moves no Rust engineering obligation into the
protocol theorem. It also introduces no new claim that BeeKEM Appendix B has
been machine-checked. BeeKEM remains an imported public theorem over its exact
game; the work specified here is the missing reduction from this protocol's
three security games to that theorem and the named standard primitive games.
