require import AllCore List FSet.
require import ProtocolTypes CanonicalEncoding ProtocolPrimitives AuthorizationState.
require import ProtocolChecks UnauthorizedSignatureReduction UnauthorizedOriginGame.
require import LiveKeyGame LiveKeyWitnesses.

import PG.

(* Positive production companion to the post-challenge reveal mutation.  The
   challenge is accepted at node 2, and the unchanged production reveal oracle
   must then reject the same node without appending another challenge query. *)
module ProductionChallengeThenRevealTrace = {
  module SO = PG.LoggedSignatureOracle(TestSignature)
  module Auth = OriginTrackedCandidateEnvironment(SO, TestNodeHash)
  module O = LiveProtocolCore(
    Auth,
    TestBeeKemLiveRuntime,
    TestMultiDomainKeySchedule,
    TestLiveKeySampler
  )

  proc main() : bool * bool * int = {
    var created : node_id option;
    var updated : node_id option;
    var challenge : live_application_key option;
    var revealed : live_application_key option;

    SO.init();
    Auth.init(live_witness_protocol_state);
    O.init(
      live_witness_protocol_state,
      1,
      true,
      authorization_digest_of empty_authorization_state
    );
    created <@ O.create_group(live_witness_creator, fset0);
    updated <@ O.send_beekem_update(live_witness_creator);
    challenge <@ O.challenge_live(live_witness_creator, NodeId 2);
    revealed <@ O.reveal_live_key(live_witness_creator, NodeId 2);

    return
      (challenge <> None,
       revealed = None,
       challenge_query_count O.queries);
  }
}.

lemma challenged_live_node_cannot_be_revealed :
  hoare [ProductionChallengeThenRevealTrace.main :
    true ==> res = (true, true, 1)].
proof.
  proc.
  inline *.
  auto.
  rewrite /live_witness_protocol_state /live_witness_creator
    /empty_active_member_store /active_member_store_put
    /active_member_store_of_set
    /empty_control_store /empty_node_digest_store
    /empty_delivery_store /empty_member_secret_store
    /empty_member_head_store /empty_causal_relation
    /control_store_put /node_digest_store_put
    /delivery_store_put /member_secret_store_put
    /member_head_store_put /node_after /test_secret_for_node
    /live_label_of /test_live_material
    /all_nodes_known /all_nodes_known_list
    /all_predecessors_delivered /all_predecessors_delivered_list
    /causal_relation_extend /predecessor_reaches_list
    /challenge_query_count /query_is_challenge /=.
  by rewrite !inE; smt().
qed.
