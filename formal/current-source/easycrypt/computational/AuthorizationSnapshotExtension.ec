require import AllCore List FSet.
require import ProtocolTypes AuthorizationState WitnessFixtures.
require import AuthorizationWitnessTrace AuthorizationWitnessTraceTail.
require import AuthorizationNormalizerWitness AuthorizationSnapshotWitnessTail.

(* Exact list-extension facts for the production normalizer's snapshot log. *)

lemma witness_initial_snapshots :
  [{| snapshot_context = fset0;
      snapshot_state = empty_authorization_state |}] =
  witness_snapshots_0.
proof.
  by rewrite /witness_snapshots_0 /witness_snapshot_0
    /witness_context_0 /witness_authorization_state_0.
qed.

lemma witness_extend_snapshots_1 :
  rcons witness_snapshots_0
    {| snapshot_context =
         witness_authorization_state_1.`as_fact_ids;
       snapshot_state = witness_authorization_state_1 |} =
  witness_snapshots_1.
proof.
  by rewrite /witness_snapshots_0 /witness_snapshots_1
    /witness_snapshot_1 /witness_authorization_state_1.
qed.

lemma witness_extend_snapshots_2 :
  rcons witness_snapshots_1
    {| snapshot_context =
         witness_authorization_state_2.`as_fact_ids;
       snapshot_state = witness_authorization_state_2 |} =
  witness_snapshots_2.
proof.
  by rewrite /witness_snapshots_1 /witness_snapshots_2
    /witness_snapshot_2 /witness_authorization_state_2.
qed.

lemma witness_extend_snapshots_3 :
  rcons witness_snapshots_2
    {| snapshot_context =
         witness_authorization_state_3.`as_fact_ids;
       snapshot_state = witness_authorization_state_3 |} =
  witness_snapshots_3.
proof.
  by rewrite /witness_snapshots_2 /witness_snapshots_3
    /witness_snapshot_3 /witness_authorization_state_3.
qed.

lemma witness_extend_snapshots_4 :
  rcons witness_snapshots_3
    {| snapshot_context =
         witness_authorization_state_4.`as_fact_ids;
       snapshot_state = witness_authorization_state_4 |} =
  witness_snapshots_4.
proof.
  by rewrite /witness_snapshots_3 /witness_snapshots_4
    /witness_snapshot_4 /witness_authorization_state_4.
qed.

lemma witness_extend_snapshots_5 :
  rcons witness_snapshots_4
    {| snapshot_context =
         witness_authorization_state_5.`as_fact_ids;
       snapshot_state = witness_authorization_state_5 |} =
  witness_snapshots_5.
proof.
  by rewrite /witness_snapshots_4 /witness_snapshots_5
    /witness_snapshot_5 /witness_authorization_state_5.
qed.

lemma witness_extend_snapshots_6 :
  rcons witness_snapshots_5
    {| snapshot_context =
         witness_authorization_state_6.`as_fact_ids;
       snapshot_state = witness_authorization_state_6 |} =
  witness_snapshots_6.
proof.
  by rewrite /witness_snapshots_5 /witness_snapshots_6
    /witness_snapshot_6 /witness_authorization_state_6.
qed.

lemma witness_extend_snapshots_7 :
  rcons witness_snapshots_6
    {| snapshot_context =
         witness_authorization_state_7.`as_fact_ids;
       snapshot_state = witness_authorization_state_7 |} =
  witness_snapshots_7.
proof.
  by rewrite /witness_snapshots_6 /witness_snapshots_7
    /witness_snapshot_7 /witness_authorization_state_7.
qed.
