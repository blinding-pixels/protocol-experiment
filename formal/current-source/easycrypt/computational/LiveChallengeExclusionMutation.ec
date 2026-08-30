require import AllCore List FSet Distr DBool.
require import ProtocolTypes CanonicalEncoding ProtocolPrimitives AuthorizationState.
require import ProtocolChecks UnauthorizedSignatureReduction UnauthorizedOriginGame.
require import LiveKeyGame LiveKeyWitnesses LivePrfGame.

import PG.

(* Narrow differential oracle used only by this anti-triviality control.  Create,
   update, and reveal are transparent calls to the production [LiveProtocolCore].
   The challenge procedure below is the production challenge admission branch
   with exactly the prior-reveal check removed.  Its hidden bit, query log, and
   challenge mark are challenger-owned and unavailable to the adversary. *)
module type REVEAL_EXCLUSION_MUTATION_ORACLE = {
  proc create_group(
    creator : principal,
    initial_members : principal fset
  ) : node_id option

  proc send_beekem_update(author : principal) : node_id option

  proc reveal_live_key(
    member : principal,
    node : node_id
  ) : live_application_key option

  proc challenge_live(
    member : principal,
    node : node_id
  ) : live_application_key option
}.

module RevealThenChallengeMutationAdversary(
  O : REVEAL_EXCLUSION_MUTATION_ORACLE
) = {
  var revealed : live_application_key option
  var challenged : live_application_key option

  proc attack() : unit = {
    var created : node_id option;
    var updated : node_id option;

    revealed <- None;
    challenged <- None;

    created <@ O.create_group(live_witness_creator, fset0);
    updated <@ O.send_beekem_update(live_witness_creator);
    revealed <@ O.reveal_live_key(live_witness_creator, NodeId 2);
    challenged <@ O.challenge_live(live_witness_creator, NodeId 2);
  }

  proc guess() : bool = {
    return
         revealed <> None
      /\ challenged <> None
      /\ revealed = challenged;
  }
}.

type reveal_exclusion_mutation_evidence = {
  reme_hidden_bit : bool;
  reme_eligible : bool;
  reme_guess : bool;
  reme_reveal_returned : bool;
  reme_challenge_returned : bool;
  reme_challenge_count : int;
  reme_win : bool
}.

module RevealExclusionRemovedGame = {
  module SO = PG.LoggedSignatureOracle(TestSignature)
  module Auth = OriginTrackedCandidateEnvironment(SO, TestNodeHash)
  module Core = LiveProtocolCore(
    Auth,
    TestBeeKemLiveRuntime,
    TestMultiDomainKeySchedule,
    TestLiveKeySampler
  )

  module MutatedOracle : REVEAL_EXCLUSION_MUTATION_ORACLE = {
    var hidden_bit : bool
    var challenged_nodes : node_id fset
    var complete_queries : live_query list

    proc init(bit : bool) : unit = {
      hidden_bit <- bit;
      challenged_nodes <- fset0;
      complete_queries <- [];
    }

    proc create_group(
      creator : principal,
      initial_members : principal fset
    ) : node_id option = {
      var result : node_id option;
      result <@ Core.create_group(creator, initial_members);
      return result;
    }

    proc send_beekem_update(author : principal) : node_id option = {
      var result : node_id option;
      result <@ Core.send_beekem_update(author);
      return result;
    }

    proc reveal_live_key(
      member : principal,
      node : node_id
    ) : live_application_key option = {
      var result : live_application_key option;
      result <@ Core.reveal_live_key(member, node);
      return result;
    }

    (* Exact production challenge body with one removed conjunct:

         node \notin Core.revealed_live_nodes

       The secret, digest, production labels, real KDF, random sampler,
       challenger bit, challenge mark, and complete query prefix are retained. *)
    proc challenge_live(
      member : principal,
      node : node_id
    ) : live_application_key option = {
      var secret_option : beekem_secret option;
      var digest_option : authorization_digest option;
      var label : live_key_label;
      var real_key : live_application_key;
      var random_key : live_application_key;
      var response : live_application_key;
      var result : live_application_key option;

      secret_option <- Core.member_secrets member node;
      digest_option <- Core.node_digests node;
      label <- witness;
      real_key <- witness;
      random_key <- witness;
      response <- witness;
      result <- None;
      complete_queries <- Core.queries;

      if (secret_option <> None /\ digest_option <> None /\
          node \notin challenged_nodes /\
          node \notin Core.challenged_live_nodes) {
        label <- live_label_of Core.public_state node (oget digest_option);
        real_key <@
          TestMultiDomainKeySchedule.derive_live(oget secret_option, label);
        random_key <@ TestLiveKeySampler.sample(label);
        response <- if hidden_bit then real_key else random_key;
        challenged_nodes <- challenged_nodes `|` fset1 node;
        complete_queries <- rcons Core.queries
          {| lq_kind = LiveChallengeQuery member;
             lq_operation = Some node |};
        result <- Some response;
      }

      return result;
    }
  }

  module A = RevealThenChallengeMutationAdversary(MutatedOracle)

  proc main_with_fixed_bit(
    hidden_bit : bool
  ) : reveal_exclusion_mutation_evidence = {
    var guess : bool;
    var eligible : bool;
    var win : bool;

    SO.init();
    Auth.init(live_witness_protocol_state);
    Core.init(
      live_witness_protocol_state,
      1,
      hidden_bit,
      authorization_digest_of empty_authorization_state
    );
    MutatedOracle.init(hidden_bit);

    A.attack();
    guess <@ A.guess();
    eligible <-
         live_trace_admissible
           1 Core.relation MutatedOracle.complete_queries Core.runtime_fault
      /\ ! Auth.unauthorized_accepted;
    win <- eligible /\ guess = hidden_bit;

    return
      {| reme_hidden_bit = hidden_bit;
         reme_eligible = eligible;
         reme_guess = guess;
         reme_reveal_returned = A.revealed <> None;
         reme_challenge_returned = A.challenged <> None;
         reme_challenge_count =
           challenge_query_count MutatedOracle.complete_queries;
         reme_win = win |};
  }

  proc main() : bool = {
    var hidden_bit : bool;
    var evidence : reveal_exclusion_mutation_evidence;

    hidden_bit <$ dbool;
    evidence <@ main_with_fixed_bit(hidden_bit);
    return evidence.`reme_win;
  }
}.

lemma reveal_exclusion_removed_fixed_real :
  hoare [RevealExclusionRemovedGame.main_with_fixed_bit :
       arg = true
    ==>
       res.`reme_win
    /\ res.`reme_eligible
    /\ res.`reme_guess
    /\ res.`reme_reveal_returned
    /\ res.`reme_challenge_returned
    /\ res.`reme_challenge_count = 1].
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
    /challenge_query_count /query_is_challenge
    /live_trace_admissible /bee_safe_kappa
    /every_challenge_safe /query_challenge_member
    /every_compromise_safe_for_challenge /query_compromise_member /=.
  by rewrite !inE; smt().
qed.

lemma reveal_exclusion_removed_fixed_random :
  hoare [RevealExclusionRemovedGame.main_with_fixed_bit :
       arg = false
    ==>
       res.`reme_win
    /\ res.`reme_eligible
    /\ ! res.`reme_guess
    /\ res.`reme_reveal_returned
    /\ res.`reme_challenge_returned
    /\ res.`reme_challenge_count = 1].
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
    /challenge_query_count /query_is_challenge
    /live_trace_admissible /bee_safe_kappa
    /every_challenge_safe /query_challenge_member
    /every_compromise_safe_for_challenge /query_compromise_member /=.
  by rewrite !inE; smt().
qed.

lemma reveal_exclusion_removed_game_probability_one &m :
  Pr[RevealExclusionRemovedGame.main() @ &m : res] = 1%r.
proof.
  byphoare => //.
  proc.
  seq 1 : true 1%r 1%r 0%r 0%r.
  + rnd.
  + case (hidden_bit).
    + call reveal_exclusion_removed_fixed_real.
      auto.
    + call reveal_exclusion_removed_fixed_random.
      auto.
qed.

lemma reveal_exclusion_removed_normalized_advantage_half &m :
  mdprf_normalized_advantage
    (Pr[RevealExclusionRemovedGame.main() @ &m : res])
    1%r = 1%r / 2%r.
proof.
  rewrite reveal_exclusion_removed_game_probability_one.
  rewrite /mdprf_normalized_advantage.
  by smt().
qed.
