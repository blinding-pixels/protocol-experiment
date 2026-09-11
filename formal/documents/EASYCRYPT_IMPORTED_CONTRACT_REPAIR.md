# BeeKEM imported-contract correction

This is a correction to the trusted primitive interface, not a new proof of
BeeKEM and not acceptance of the complete application theorem.

## Primary source and scope

The existing pinned paper is Yen et al., *BeeKEM*, ePrint 2026/1434. Its PDF was
retrieved in GitHub Actions run 34542305583 and its bytes match the existing
manifest SHA-256:
`129a819400898536455cabe4ba104c02d902384ea802b4900a388e8e9c0e4fb3`.
Section 5, page 10 gives the adversary oracle access and public message access.
Figure 8, page 18 samples the private challenge bit and calls the adversary
through those oracles; it does not expose the bit or writable challenger state.
Theorem 1 is explicitly for `Pi = BeeKEM[SE, NIKE]`, not every protocol sharing
a procedure signature. Appendix B's security reduction remains trusted.

## Corrected contract

The imported axiom now quantifies over KI adversaries with free-access exclusions
for `BeeKemKiOracles` and `BeeKemOracleEnvironment`. Calls through the supplied
oracle parameter remain allowed, including create/add/remove/update/deliver,
reveal/challenge/compromise and both public message accessors. Private-bit reads,
private-state reads or writes, and calls bypassing the supplied oracle are not
permitted. The same exclusions propagate through the actual fixed-bit and
sampled application-derived adversaries and their bound consumers.

The existential NIKE and encryption reduction adversaries also exclude their
respective primitive challenger's private globals. Without those restrictions,
a bound naming existential adversaries would not support an appeal to
oracle-only primitive security.

`BEEKEM_PAPER_INSTANCE` remains a generic adapter/testing surface; that type does
not prove that an arbitrary implementation is BeeKEM. The security import is
now fixed to `PublishedBeeKemInstance`. Its twelve opaque transition
probabilities represent the imported paper construction and its own primitive
algorithms. They contain no challenger globals. This is an ABSTRACT PRIMITIVE
INTERFACE, not a verified implementation or a reimplementation of Appendix B.
No new security axiom is introduced: the existing named paper theorem is the
sole imported security result and relates this fixed primitive to its own
NIKE/SE games. The generic adapters and fixture algorithms remain unchanged.

This deliberately removes the old unsupported universal quantification over an
arbitrary `I : BEEKEM_PAPER_INSTANCE` from the bound-bearing theorems. A concrete
implementation is not automatically covered merely by implementing that type;
its correspondence to the imported functionality must be justified separately.
Generic simulation lemmas retain their generic implementation parameters where
they do not use the imported security theorem.

The exact numeric loss expressions, perfect-correctness specialization,
all-safe premise, counters and finite-retention conditions are unchanged. The
old centered-normalization interpretation and its source caveat remain in the
manifest; this correction does not silently resolve unrelated model questions.

## Checks and their limitations

Focused fresh pinned-runtime checks accept the construction interface, the
imported axiom file, both concrete application-to-BeeKEM theorem applications,
the primitive-bound consumer, the sampled bound, and the final-bound file.
The public entries also compile. These checks are NOT a complete dependency
closure certification.

The quarantined original counterexample still independently checks without the
security axiom. Applying the corrected imported theorem to its forbidden actor
is now rejected for private-state access, not for an assumed false premise.
The imported theorem's changed arity is reflected in that regression call.

Additional generated controls elaborate the ACTUAL imported theorem: a constant
actor and an actor invoking all ten supplied oracles are admitted; direct bit
read/write, direct protocol-state read/write, and a bypass call are rejected for
private access. These are type-admission tests, not assertions that every
possible oracle schedule satisfies the safety predicate. A separate axiom-free
probability theorem proves the usual one-half no-query baseline for the named
published interface in the empty-initial-user experiment. Existing nonempty
fixture reachability and compromise-rejection controls remain independent.

The computational source audit now requires the corrected private exclusions,
fixed construction binding, and restricted existential reduction interfaces.
The existing mutation/vacuity generators were updated ONLY for the new theorem
arity/binder text; their bad conclusions and loss-removal sites are retained.
The new imported-boundary job complements rather than replaces the existing
vacuity and direct-closure checks.

Known false auxiliary wrapper/control claims and unrelated proof-body failures
remain. In particular the old `LiveBeeKemAuthoritativeComposition` simulation
still fails at its original `sim` step; its theorem scope is corrected here,
but its proof body is not reported repaired. No claim of global consistency or
completed L0-L4 security follows from rejecting this particular reproducer.
