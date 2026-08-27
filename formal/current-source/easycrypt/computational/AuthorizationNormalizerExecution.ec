require import AllCore List FSet.
require import ProtocolTypes CanonicalEncoding ProtocolPrimitives AuthorizationState WitnessFixtures.
require import AuthorizationWitnessTrace AuthorizationWitnessTraceTail.
require import AuthorizationNormalizerWitness AuthorizationSnapshotWitnessTail.
require import AuthorizationSnapshotExtension.

(* Small executable contracts for the exact honest normalization trace.  The
   prefix ladder establishes the proof pattern before the seven-fact result is
   used as a call contract by the production validator proof. *)

op witness_signed_facts_1 : signed_authorization_fact list =
  [witness_signed_fact_1].

op witness_signed_facts_2 : signed_authorization_fact list =
  [witness_signed_fact_1; witness_signed_fact_2].

lemma witness_empty_state_0 :
  empty_authorization_state = witness_authorization_state_0.
proof.
  by rewrite /witness_authorization_state_0.
qed.

lemma witness_fact_1_context_projection :
  witness_fact_1.`af_context = witness_context_0.
proof.
  by rewrite /witness_fact_1.
qed.

lemma witness_fact_2_context_projection :
  witness_fact_2.`af_context = witness_context_1.
proof.
  by rewrite /witness_fact_2.
qed.

lemma normalize_witness_prefix_1 :
  hoare [NormalizeAuthorization(TestSignature).normalize :
    facts = witness_signed_facts_1 /\ creator = witness_alice ==>
    res = (true, witness_authorization_state_1)].
proof.
  proc.
  inline TestSignature.verify.
  rcondt ^while; first by
    auto; rewrite /witness_signed_facts_1.
  rcondf ^while.
  + auto;
    rewrite /witness_signed_facts_1
      /witness_signed_fact_1 /witness_signed_fact_of
      witness_empty_state_0 witness_initial_snapshots
      witness_fact_1_context_projection
      witness_lookup_context_0 witness_fact_1_transition
      witness_extend_snapshots_1.
  auto;
  rewrite /witness_signed_facts_1
    /witness_signed_fact_1 /witness_signed_fact_of
    witness_empty_state_0 witness_initial_snapshots.
  move=> &hr [facts_hr creator_hr].
  rewrite facts_hr creator_hr /=
    witness_fact_1_context_projection
    witness_lookup_context_0 witness_fact_1_transition.
  by [].
qed.

lemma normalize_witness_prefix_2 :
  hoare [NormalizeAuthorization(TestSignature).normalize :
    facts = witness_signed_facts_2 /\ creator = witness_alice ==>
    res = (true, witness_authorization_state_2)].
proof.
  proc.
  inline TestSignature.verify.
  rcondt ^while; first by
    auto; rewrite /witness_signed_facts_2.
  rcondt ^while; first by
    auto;
    rewrite /witness_signed_facts_2
      /witness_signed_fact_1 /witness_signed_fact_of
      witness_empty_state_0 witness_initial_snapshots
      witness_lookup_context_0 witness_fact_1_transition
      witness_extend_snapshots_1.
  rcondf ^while.
  + auto;
    rewrite /witness_signed_facts_2
      /witness_signed_fact_1 /witness_signed_fact_2
      /witness_signed_fact_of
      witness_empty_state_0 witness_initial_snapshots
      witness_fact_1_context_projection
      witness_lookup_context_0 witness_fact_1_transition
      witness_extend_snapshots_1
      witness_fact_2_context_projection
      witness_lookup_context_1 witness_fact_2_transition
      witness_extend_snapshots_2.
  auto;
  rewrite /witness_signed_facts_2
    /witness_signed_fact_1 /witness_signed_fact_2
    /witness_signed_fact_of
    witness_empty_state_0 witness_initial_snapshots.
  move=> &hr [facts_hr creator_hr].
  rewrite facts_hr creator_hr /=
    witness_fact_1_context_projection
    witness_lookup_context_0 witness_fact_1_transition
    witness_extend_snapshots_1
    witness_fact_2_context_projection
    witness_lookup_context_1 witness_fact_2_transition.
  by [].
qed.
