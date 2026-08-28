require import AllCore List FSet.
require import ProtocolTypes AuthorizationState WitnessFixtures.
require import AuthorizationWitnessTrace AuthorizationWitnessTraceTail.
require import AuthorizationNormalizerWitness.

(* Exact separation and lookup facts for the remaining honest-prefix snapshots. *)

lemma witness_context_0_neq_3 :
  witness_context_0 <> witness_context_3.
proof.
  rewrite /witness_context_0 /witness_context_3 /witness_context_2
    /witness_context_1 /witness_fact_id_1 /witness_fact_id_2
    /witness_fact_id_3.
  smt(in_fset0 in_fset1 in_fsetU).
qed.

lemma witness_context_1_neq_3 :
  witness_context_1 <> witness_context_3.
proof.
  rewrite /witness_context_3 /witness_context_2 /witness_context_1
    /witness_fact_id_1 /witness_fact_id_2 /witness_fact_id_3.
  smt(in_fset1 in_fsetU).
qed.

lemma witness_context_2_neq_3 :
  witness_context_2 <> witness_context_3.
proof.
  rewrite /witness_context_3 /witness_context_2 /witness_context_1
    /witness_fact_id_1 /witness_fact_id_2 /witness_fact_id_3.
  smt(in_fset1 in_fsetU).
qed.

lemma witness_lookup_context_3 :
  authorization_snapshot_lookup
    witness_context_3 witness_snapshots_3 =
  Some witness_authorization_state_3.
proof.
  rewrite /witness_snapshots_3
    /witness_snapshot_0 /witness_snapshot_1
    /witness_snapshot_2 /witness_snapshot_3.
  by smt(witness_context_0_neq_3 witness_context_1_neq_3
    witness_context_2_neq_3).
qed.

lemma witness_context_0_neq_4 :
  witness_context_0 <> witness_context_4.
proof.
  rewrite /witness_context_0 /witness_context_4 /witness_context_3
    /witness_context_2 /witness_context_1
    /witness_fact_id_1 /witness_fact_id_2 /witness_fact_id_3
    /witness_fact_id_4.
  smt(in_fset0 in_fset1 in_fsetU).
qed.

lemma witness_context_1_neq_4 :
  witness_context_1 <> witness_context_4.
proof.
  rewrite /witness_context_4 /witness_context_3 /witness_context_2
    /witness_context_1 /witness_fact_id_1 /witness_fact_id_2
    /witness_fact_id_3 /witness_fact_id_4.
  smt(in_fset1 in_fsetU).
qed.

lemma witness_context_2_neq_4 :
  witness_context_2 <> witness_context_4.
proof.
  rewrite /witness_context_4 /witness_context_3 /witness_context_2
    /witness_context_1 /witness_fact_id_1 /witness_fact_id_2
    /witness_fact_id_3 /witness_fact_id_4.
  smt(in_fset1 in_fsetU).
qed.

lemma witness_context_3_neq_4 :
  witness_context_3 <> witness_context_4.
proof.
  rewrite /witness_context_4 /witness_context_3 /witness_context_2
    /witness_context_1 /witness_fact_id_1 /witness_fact_id_2
    /witness_fact_id_3 /witness_fact_id_4.
  smt(in_fset1 in_fsetU).
qed.

lemma witness_lookup_context_4 :
  authorization_snapshot_lookup
    witness_context_4 witness_snapshots_4 =
  Some witness_authorization_state_4.
proof.
  rewrite /witness_snapshots_4
    /witness_snapshot_0 /witness_snapshot_1 /witness_snapshot_2
    /witness_snapshot_3 /witness_snapshot_4.
  by smt(witness_context_0_neq_4 witness_context_1_neq_4
    witness_context_2_neq_4 witness_context_3_neq_4).
qed.

lemma witness_context_0_neq_5 :
  witness_context_0 <> witness_context_5.
proof.
  rewrite /witness_context_0 /witness_context_5 /witness_context_4
    /witness_context_3 /witness_context_2 /witness_context_1
    /witness_fact_id_1 /witness_fact_id_2 /witness_fact_id_3
    /witness_fact_id_4 /witness_fact_id_5.
  smt(in_fset0 in_fset1 in_fsetU).
qed.

lemma witness_context_1_neq_5 :
  witness_context_1 <> witness_context_5.
proof.
  rewrite /witness_context_5 /witness_context_4 /witness_context_3
    /witness_context_2 /witness_context_1
    /witness_fact_id_1 /witness_fact_id_2 /witness_fact_id_3
    /witness_fact_id_4 /witness_fact_id_5.
  smt(in_fset1 in_fsetU).
qed.

lemma witness_context_2_neq_5 :
  witness_context_2 <> witness_context_5.
proof.
  rewrite /witness_context_5 /witness_context_4 /witness_context_3
    /witness_context_2 /witness_context_1
    /witness_fact_id_1 /witness_fact_id_2 /witness_fact_id_3
    /witness_fact_id_4 /witness_fact_id_5.
  smt(in_fset1 in_fsetU).
qed.

lemma witness_context_3_neq_5 :
  witness_context_3 <> witness_context_5.
proof.
  rewrite /witness_context_5 /witness_context_4 /witness_context_3
    /witness_context_2 /witness_context_1
    /witness_fact_id_1 /witness_fact_id_2 /witness_fact_id_3
    /witness_fact_id_4 /witness_fact_id_5.
  smt(in_fset1 in_fsetU).
qed.

lemma witness_context_4_neq_5 :
  witness_context_4 <> witness_context_5.
proof.
  rewrite /witness_context_5 /witness_context_4 /witness_context_3
    /witness_context_2 /witness_context_1
    /witness_fact_id_1 /witness_fact_id_2 /witness_fact_id_3
    /witness_fact_id_4 /witness_fact_id_5.
  smt(in_fset1 in_fsetU).
qed.

lemma witness_lookup_context_5 :
  authorization_snapshot_lookup
    witness_context_5 witness_snapshots_5 =
  Some witness_authorization_state_5.
proof.
  rewrite /witness_snapshots_5
    /witness_snapshot_0 /witness_snapshot_1 /witness_snapshot_2
    /witness_snapshot_3 /witness_snapshot_4 /witness_snapshot_5.
  by smt(witness_context_0_neq_5 witness_context_1_neq_5
    witness_context_2_neq_5 witness_context_3_neq_5
    witness_context_4_neq_5).
qed.

lemma witness_context_0_neq_6 :
  witness_context_0 <> witness_context_6.
proof.
  rewrite /witness_context_0 /witness_context_6 /witness_context_5
    /witness_context_4 /witness_context_3 /witness_context_2
    /witness_context_1 /witness_fact_id_1 /witness_fact_id_2
    /witness_fact_id_3 /witness_fact_id_4 /witness_fact_id_5
    /witness_fact_id_6.
  smt(in_fset0 in_fset1 in_fsetU).
qed.

lemma witness_context_1_neq_6 :
  witness_context_1 <> witness_context_6.
proof.
  rewrite /witness_context_6 /witness_context_5 /witness_context_4
    /witness_context_3 /witness_context_2 /witness_context_1
    /witness_fact_id_1 /witness_fact_id_2 /witness_fact_id_3
    /witness_fact_id_4 /witness_fact_id_5 /witness_fact_id_6.
  smt(in_fset1 in_fsetU).
qed.

lemma witness_context_2_neq_6 :
  witness_context_2 <> witness_context_6.
proof.
  rewrite /witness_context_6 /witness_context_5 /witness_context_4
    /witness_context_3 /witness_context_2 /witness_context_1
    /witness_fact_id_1 /witness_fact_id_2 /witness_fact_id_3
    /witness_fact_id_4 /witness_fact_id_5 /witness_fact_id_6.
  smt(in_fset1 in_fsetU).
qed.

lemma witness_context_3_neq_6 :
  witness_context_3 <> witness_context_6.
proof.
  rewrite /witness_context_6 /witness_context_5 /witness_context_4
    /witness_context_3 /witness_context_2 /witness_context_1
    /witness_fact_id_1 /witness_fact_id_2 /witness_fact_id_3
    /witness_fact_id_4 /witness_fact_id_5 /witness_fact_id_6.
  smt(in_fset1 in_fsetU).
qed.

lemma witness_context_4_neq_6 :
  witness_context_4 <> witness_context_6.
proof.
  rewrite /witness_context_6 /witness_context_5 /witness_context_4
    /witness_context_3 /witness_context_2 /witness_context_1
    /witness_fact_id_1 /witness_fact_id_2 /witness_fact_id_3
    /witness_fact_id_4 /witness_fact_id_5 /witness_fact_id_6.
  smt(in_fset1 in_fsetU).
qed.

lemma witness_context_5_neq_6 :
  witness_context_5 <> witness_context_6.
proof.
  rewrite /witness_context_6 /witness_context_5 /witness_context_4
    /witness_context_3 /witness_context_2 /witness_context_1
    /witness_fact_id_1 /witness_fact_id_2 /witness_fact_id_3
    /witness_fact_id_4 /witness_fact_id_5 /witness_fact_id_6.
  smt(in_fset1 in_fsetU).
qed.

lemma witness_lookup_context_6 :
  authorization_snapshot_lookup
    witness_context_6 witness_snapshots_6 =
  Some witness_authorization_state_6.
proof.
  rewrite /witness_snapshots_6
    /witness_snapshot_0 /witness_snapshot_1 /witness_snapshot_2
    /witness_snapshot_3 /witness_snapshot_4 /witness_snapshot_5
    /witness_snapshot_6.
  by smt(witness_context_0_neq_6 witness_context_1_neq_6
    witness_context_2_neq_6 witness_context_3_neq_6
    witness_context_4_neq_6 witness_context_5_neq_6).
qed.

lemma witness_context_0_neq_7 :
  witness_context_0 <> witness_context_7.
proof.
  rewrite /witness_context_0 /witness_context_7 /witness_context_6
    /witness_context_5 /witness_context_4 /witness_context_3
    /witness_context_2 /witness_context_1
    /witness_fact_id_1 /witness_fact_id_2 /witness_fact_id_3
    /witness_fact_id_4 /witness_fact_id_5 /witness_fact_id_6
    /witness_fact_id_7.
  smt(in_fset0 in_fset1 in_fsetU).
qed.

lemma witness_context_1_neq_7 :
  witness_context_1 <> witness_context_7.
proof.
  rewrite /witness_context_7 /witness_context_6 /witness_context_5
    /witness_context_4 /witness_context_3 /witness_context_2
    /witness_context_1 /witness_fact_id_1 /witness_fact_id_2
    /witness_fact_id_3 /witness_fact_id_4 /witness_fact_id_5
    /witness_fact_id_6 /witness_fact_id_7.
  smt(in_fset1 in_fsetU).
qed.

lemma witness_context_2_neq_7 :
  witness_context_2 <> witness_context_7.
proof.
  rewrite /witness_context_7 /witness_context_6 /witness_context_5
    /witness_context_4 /witness_context_3 /witness_context_2
    /witness_context_1 /witness_fact_id_1 /witness_fact_id_2
    /witness_fact_id_3 /witness_fact_id_4 /witness_fact_id_5
    /witness_fact_id_6 /witness_fact_id_7.
  smt(in_fset1 in_fsetU).
qed.

lemma witness_context_3_neq_7 :
  witness_context_3 <> witness_context_7.
proof.
  rewrite /witness_context_7 /witness_context_6 /witness_context_5
    /witness_context_4 /witness_context_3 /witness_context_2
    /witness_context_1 /witness_fact_id_1 /witness_fact_id_2
    /witness_fact_id_3 /witness_fact_id_4 /witness_fact_id_5
    /witness_fact_id_6 /witness_fact_id_7.
  smt(in_fset1 in_fsetU).
qed.

lemma witness_context_4_neq_7 :
  witness_context_4 <> witness_context_7.
proof.
  rewrite /witness_context_7 /witness_context_6 /witness_context_5
    /witness_context_4 /witness_context_3 /witness_context_2
    /witness_context_1 /witness_fact_id_1 /witness_fact_id_2
    /witness_fact_id_3 /witness_fact_id_4 /witness_fact_id_5
    /witness_fact_id_6 /witness_fact_id_7.
  smt(in_fset1 in_fsetU).
qed.

lemma witness_context_5_neq_7 :
  witness_context_5 <> witness_context_7.
proof.
  rewrite /witness_context_7 /witness_context_6 /witness_context_5
    /witness_context_4 /witness_context_3 /witness_context_2
    /witness_context_1 /witness_fact_id_1 /witness_fact_id_2
    /witness_fact_id_3 /witness_fact_id_4 /witness_fact_id_5
    /witness_fact_id_6 /witness_fact_id_7.
  smt(in_fset1 in_fsetU).
qed.

lemma witness_context_6_neq_7 :
  witness_context_6 <> witness_context_7.
proof.
  rewrite /witness_context_7 /witness_context_6 /witness_context_5
    /witness_context_4 /witness_context_3 /witness_context_2
    /witness_context_1 /witness_fact_id_1 /witness_fact_id_2
    /witness_fact_id_3 /witness_fact_id_4 /witness_fact_id_5
    /witness_fact_id_6 /witness_fact_id_7.
  smt(in_fset1 in_fsetU).
qed.

lemma witness_lookup_context_7 :
  authorization_snapshot_lookup
    witness_context_7 witness_snapshots_7 =
  Some witness_authorization_state_7.
proof.
  rewrite /witness_snapshots_7
    /witness_snapshot_0 /witness_snapshot_1 /witness_snapshot_2
    /witness_snapshot_3 /witness_snapshot_4 /witness_snapshot_5
    /witness_snapshot_6 /witness_snapshot_7.
  by smt(witness_context_0_neq_7 witness_context_1_neq_7
    witness_context_2_neq_7 witness_context_3_neq_7
    witness_context_4_neq_7 witness_context_5_neq_7
    witness_context_6_neq_7).
qed.
