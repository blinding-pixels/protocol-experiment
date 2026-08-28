require import AllCore List FSet.
require import ProtocolTypes CanonicalEncoding ProtocolPrimitives AuthorizationState WitnessFixtures.
require import AuthorizationWitnessTrace AuthorizationWitnessTraceTail.
require import AuthorizationNormalizerWitness AuthorizationSnapshotWitnessTail.
require import AuthorizationSnapshotExtension AuthorizationNormalizerExecution.
require import AuthorizationNormalizerExecutionTail AuthorizationNormalizerExecutionFinal.

(* Complete seven-fact execution contract for the honest base authorization
   trace.  Earlier prefix theories remain independently kernel-checkable. *)

op witness_signed_facts_7 : signed_authorization_fact list =
  [witness_signed_fact_1; witness_signed_fact_2; witness_signed_fact_3;
   witness_signed_fact_4; witness_signed_fact_5; witness_signed_fact_6;
   witness_signed_fact_7].

lemma witness_fact_7_context_projection :
  witness_fact_7.`af_context = witness_context_6.
proof.
  by rewrite /witness_fact_7.
qed.

lemma normalize_witness_prefix_7 :
  hoare [NormalizeAuthorization(TestSignature).normalize :
    facts = witness_signed_facts_7 /\ creator = witness_alice ==>
    res = (true, witness_authorization_state_7)].
proof.
  proc.
  inline TestSignature.verify.
  rcondt ^while; first by
    auto; rewrite /witness_signed_facts_7.
  rcondt ^while; first by
    auto;
    rewrite /witness_signed_facts_7
      /witness_signed_fact_1 /witness_signed_fact_of
      witness_empty_state_0 witness_initial_snapshots;
    smt(witness_lookup_context_0
        witness_fact_1_transition
        witness_extend_snapshots_1).
  rcondt ^while; first by
    auto;
    rewrite /witness_signed_facts_7
      /witness_signed_fact_1 /witness_signed_fact_2
      /witness_signed_fact_of
      witness_empty_state_0 witness_initial_snapshots;
    smt(witness_fact_1_context_projection
        witness_lookup_context_0
        witness_fact_1_transition
        witness_extend_snapshots_1
        witness_fact_2_context_projection
        witness_lookup_context_1
        witness_fact_2_transition
        witness_extend_snapshots_2).
  rcondt ^while; first by
    auto;
    rewrite /witness_signed_facts_7
      /witness_signed_fact_1 /witness_signed_fact_2
      /witness_signed_fact_3 /witness_signed_fact_of
      witness_empty_state_0 witness_initial_snapshots;
    smt(witness_fact_1_context_projection
        witness_lookup_context_0
        witness_fact_1_transition
        witness_extend_snapshots_1
        witness_fact_2_context_projection
        witness_lookup_context_1
        witness_fact_2_transition
        witness_extend_snapshots_2
        witness_fact_3_context_projection
        witness_lookup_context_2
        witness_fact_3_transition
        witness_extend_snapshots_3).
  rcondt ^while; first by
    auto;
    rewrite /witness_signed_facts_7
      /witness_signed_fact_1 /witness_signed_fact_2
      /witness_signed_fact_3 /witness_signed_fact_4
      /witness_signed_fact_of
      witness_empty_state_0 witness_initial_snapshots;
    smt(witness_fact_1_context_projection
        witness_lookup_context_0
        witness_fact_1_transition
        witness_extend_snapshots_1
        witness_fact_2_context_projection
        witness_lookup_context_1
        witness_fact_2_transition
        witness_extend_snapshots_2
        witness_fact_3_context_projection
        witness_lookup_context_2
        witness_fact_3_transition
        witness_extend_snapshots_3
        witness_fact_4_context_projection
        witness_lookup_context_3
        witness_fact_4_transition
        witness_extend_snapshots_4).
  rcondt ^while; first by
    auto;
    rewrite /witness_signed_facts_7
      /witness_signed_fact_1 /witness_signed_fact_2
      /witness_signed_fact_3 /witness_signed_fact_4
      /witness_signed_fact_5 /witness_signed_fact_of
      witness_empty_state_0 witness_initial_snapshots;
    smt(witness_fact_1_context_projection
        witness_lookup_context_0
        witness_fact_1_transition
        witness_extend_snapshots_1
        witness_fact_2_context_projection
        witness_lookup_context_1
        witness_fact_2_transition
        witness_extend_snapshots_2
        witness_fact_3_context_projection
        witness_lookup_context_2
        witness_fact_3_transition
        witness_extend_snapshots_3
        witness_fact_4_context_projection
        witness_lookup_context_3
        witness_fact_4_transition
        witness_extend_snapshots_4
        witness_fact_5_context_projection
        witness_lookup_context_4
        witness_fact_5_transition
        witness_extend_snapshots_5).
  rcondt ^while; first by
    auto;
    rewrite /witness_signed_facts_7
      /witness_signed_fact_1 /witness_signed_fact_2
      /witness_signed_fact_3 /witness_signed_fact_4
      /witness_signed_fact_5 /witness_signed_fact_6
      /witness_signed_fact_of
      witness_empty_state_0 witness_initial_snapshots;
    smt(witness_fact_1_context_projection
        witness_lookup_context_0
        witness_fact_1_transition
        witness_extend_snapshots_1
        witness_fact_2_context_projection
        witness_lookup_context_1
        witness_fact_2_transition
        witness_extend_snapshots_2
        witness_fact_3_context_projection
        witness_lookup_context_2
        witness_fact_3_transition
        witness_extend_snapshots_3
        witness_fact_4_context_projection
        witness_lookup_context_3
        witness_fact_4_transition
        witness_extend_snapshots_4
        witness_fact_5_context_projection
        witness_lookup_context_4
        witness_fact_5_transition
        witness_extend_snapshots_5
        witness_fact_6_context_projection
        witness_lookup_context_5
        witness_fact_6_transition
        witness_extend_snapshots_6).
  rcondf ^while.
  + auto;
    rewrite /witness_signed_facts_7
      /witness_signed_fact_1 /witness_signed_fact_2
      /witness_signed_fact_3 /witness_signed_fact_4
      /witness_signed_fact_5 /witness_signed_fact_6
      /witness_signed_fact_7 /witness_signed_fact_of
      witness_empty_state_0 witness_initial_snapshots;
    smt(witness_fact_1_context_projection
        witness_lookup_context_0
        witness_fact_1_transition
        witness_extend_snapshots_1
        witness_fact_2_context_projection
        witness_lookup_context_1
        witness_fact_2_transition
        witness_extend_snapshots_2
        witness_fact_3_context_projection
        witness_lookup_context_2
        witness_fact_3_transition
        witness_extend_snapshots_3
        witness_fact_4_context_projection
        witness_lookup_context_3
        witness_fact_4_transition
        witness_extend_snapshots_4
        witness_fact_5_context_projection
        witness_lookup_context_4
        witness_fact_5_transition
        witness_extend_snapshots_5
        witness_fact_6_context_projection
        witness_lookup_context_5
        witness_fact_6_transition
        witness_extend_snapshots_6
        witness_fact_7_context_projection
        witness_lookup_context_6
        witness_fact_7_transition
        witness_extend_snapshots_7).
  auto;
  rewrite /witness_signed_facts_7
    /witness_signed_fact_1 /witness_signed_fact_2
    /witness_signed_fact_3 /witness_signed_fact_4
    /witness_signed_fact_5 /witness_signed_fact_6
    /witness_signed_fact_7 /witness_signed_fact_of
    witness_empty_state_0 witness_initial_snapshots.
  move=> &hr [facts_hr creator_hr].
  rewrite facts_hr creator_hr /=
    witness_fact_1_context_projection
    witness_lookup_context_0 witness_fact_1_transition
    witness_extend_snapshots_1
    witness_fact_2_context_projection
    witness_lookup_context_1 witness_fact_2_transition
    witness_extend_snapshots_2
    witness_fact_3_context_projection
    witness_lookup_context_2 witness_fact_3_transition
    witness_extend_snapshots_3
    witness_fact_4_context_projection
    witness_lookup_context_3 witness_fact_4_transition
    witness_extend_snapshots_4
    witness_fact_5_context_projection
    witness_lookup_context_4 witness_fact_5_transition
    witness_extend_snapshots_5
    witness_fact_6_context_projection
    witness_lookup_context_5 witness_fact_6_transition
    witness_extend_snapshots_6
    witness_fact_7_context_projection
    witness_lookup_context_6 witness_fact_7_transition.
  by [].
qed.
