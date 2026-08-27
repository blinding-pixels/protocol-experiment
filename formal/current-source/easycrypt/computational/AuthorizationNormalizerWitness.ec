require import AllCore List FSet.
require import ProtocolTypes CanonicalEncoding ProtocolPrimitives AuthorizationState.
require import WitnessFixtures AuthorizationWitnessTrace AuthorizationWitnessTraceTail.

(* Termination is independent of the concrete honest fixture: every loop
   iteration removes one signed fact before any validation branch is taken. *)
lemma normalize_test_signature_lossless :
  islossless NormalizeAuthorization(TestSignature).normalize.
proof.
  proc.
  while (true) (size remaining).
  - move=> z.
    inline TestSignature.verify.
    auto => />.
    smt(size_behead size_ge0).
  - by auto; smt(size_ge0).
qed.

op witness_snapshot_0 : authorization_snapshot =
  {| snapshot_context = witness_context_0;
     snapshot_state = witness_authorization_state_0 |}.

op witness_snapshot_1 : authorization_snapshot =
  {| snapshot_context = witness_context_1;
     snapshot_state = witness_authorization_state_1 |}.

op witness_snapshot_2 : authorization_snapshot =
  {| snapshot_context = witness_context_2;
     snapshot_state = witness_authorization_state_2 |}.

op witness_snapshot_3 : authorization_snapshot =
  {| snapshot_context = witness_context_3;
     snapshot_state = witness_authorization_state_3 |}.

op witness_snapshot_4 : authorization_snapshot =
  {| snapshot_context = witness_context_4;
     snapshot_state = witness_authorization_state_4 |}.

op witness_snapshot_5 : authorization_snapshot =
  {| snapshot_context = witness_context_5;
     snapshot_state = witness_authorization_state_5 |}.

op witness_snapshot_6 : authorization_snapshot =
  {| snapshot_context = witness_context_6;
     snapshot_state = witness_authorization_state_6 |}.

op witness_snapshot_7 : authorization_snapshot =
  {| snapshot_context = witness_context_7;
     snapshot_state = witness_authorization_state_7 |}.

op witness_snapshots_0 : authorization_snapshot list =
  [witness_snapshot_0].

op witness_snapshots_1 : authorization_snapshot list =
  [witness_snapshot_0; witness_snapshot_1].

op witness_snapshots_2 : authorization_snapshot list =
  [witness_snapshot_0; witness_snapshot_1; witness_snapshot_2].

op witness_snapshots_3 : authorization_snapshot list =
  [witness_snapshot_0; witness_snapshot_1; witness_snapshot_2;
   witness_snapshot_3].

op witness_snapshots_4 : authorization_snapshot list =
  [witness_snapshot_0; witness_snapshot_1; witness_snapshot_2;
   witness_snapshot_3; witness_snapshot_4].

op witness_snapshots_5 : authorization_snapshot list =
  [witness_snapshot_0; witness_snapshot_1; witness_snapshot_2;
   witness_snapshot_3; witness_snapshot_4; witness_snapshot_5].

op witness_snapshots_6 : authorization_snapshot list =
  [witness_snapshot_0; witness_snapshot_1; witness_snapshot_2;
   witness_snapshot_3; witness_snapshot_4; witness_snapshot_5;
   witness_snapshot_6].

op witness_snapshots_7 : authorization_snapshot list =
  [witness_snapshot_0; witness_snapshot_1; witness_snapshot_2;
   witness_snapshot_3; witness_snapshot_4; witness_snapshot_5;
   witness_snapshot_6; witness_snapshot_7].

lemma witness_lookup_context_0 :
  authorization_snapshot_lookup
    witness_context_0 witness_snapshots_0 =
  Some witness_authorization_state_0.
proof.
  by rewrite /authorization_snapshot_lookup /witness_snapshots_0
    /witness_snapshot_0.
qed.

lemma witness_lookup_context_1 :
  authorization_snapshot_lookup
    witness_context_1 witness_snapshots_1 =
  Some witness_authorization_state_1.
proof.
  rewrite /authorization_snapshot_lookup /witness_snapshots_1
    /witness_snapshot_0 /witness_snapshot_1
    /witness_context_0 /witness_context_1 /witness_fact_id_1.
  by smt(in_fset0 in_fset1).
qed.

lemma witness_context_0_neq_2 :
  witness_context_0 <> witness_context_2.
proof.
  rewrite /witness_context_0 /witness_context_2 /witness_context_1
    /witness_fact_id_1 /witness_fact_id_2.
  smt(in_fset0 in_fset1 in_fsetU).
qed.

lemma witness_context_1_neq_2 :
  witness_context_1 <> witness_context_2.
proof.
  rewrite /witness_context_2 /witness_context_1
    /witness_fact_id_1 /witness_fact_id_2.
  smt(in_fset1 in_fsetU).
qed.

lemma witness_lookup_context_2 :
  authorization_snapshot_lookup
    witness_context_2 witness_snapshots_2 =
  Some witness_authorization_state_2.
proof.
  by rewrite /authorization_snapshot_lookup /witness_snapshots_2
    /witness_snapshot_0 /witness_snapshot_1 /witness_snapshot_2
    witness_context_0_neq_2 witness_context_1_neq_2.
qed.
