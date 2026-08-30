require import AllCore List FSet Distr DBool.
require import ProtocolTypes CanonicalEncoding ProtocolPrimitives AuthorizationState.
require import ProtocolChecks UnauthorizedSignatureReduction UnauthorizedOriginGame.
require import LiveKeyGame LiveKeyWitnesses LivePrfGame.

import PG.

(* Narrow differential oracle used only by this anti-triviality control.  Create,
   update, and challenge are transparent calls to the production
   [LiveProtocolCore].  The reveal procedure below is the production reveal
   admission branch with exactly the prior-challenge check removed.  Its query
   log and reveal mark remain challenger-owned and unavailable to the adversary. *)
module type POST_CHALLENGE_REVEAL_MUTATION_ORACLE = {
  proc create_group(
    creator : principal,
    initial_members : principal fset
  ) : node_id option

  proc send_beekem_update(author : principal) : node_id option

  proc challenge_live(
    member : principal,
    node : node_id
  ) : live_application_key option

  proc reveal_live_key(
    member : principal,
    node : node_id
  ) : live_application_key option
}.

module ChallengeThenRevealMutationAdversary(
  O : POST_CHALLENGE_REVEAL_MUTATION_ORACLE
) = {
  var challenged : live_application_key option
  var revealed : live_application_key option

  proc attack() : unit = {
    var created : node_id option;
    var updated : node_id option;

    challenged <- None;
    revealed <- None;

    created <@ O.create_group(live_witness_creator, fset0);
    updated <@ O.send_beekem_update(live_witness_creator);
    challenged <@ O.challenge_live(live_witness_creator, NodeId 2);
    revealed <@ O.reveal_live_key(live_witness_creator, NodeId 2);
  }

  proc guess() : bool = {
    return
         challenged <> None
      /\ revealed <> None
      /\ challenged = revealed;
  }
}.

type post_challenge_reveal_mutation_evidence = {
  pcre_hidden_bit : bool;
  pcre_eligible : bool;
  pcre_guess : bool;
  pcre_challenge_returned : bool;
  pcre_reveal_returned : bool;
  pcre_challenge_count : int;
  pcre_win : bool
}.

module PostChallengeRevealExclusionRemovedGame = {
  module SO = PG.LoggedSignatureOracle(TestSignature)
  module Auth = OriginTrackedCandidateEnvironment(SO, TestNodeHash)
  module Core = LiveProtocolCore(
    Auth,
    TestBeeKemLiveRuntime,
    TestMultiDomainKeySchedule,
    TestLiveKeySampler
  )

  module MutatedOracle : POST_CHALLENGE_REVEAL_MUTATION_ORACLE = {
    var revealed_nodes : node_id fset
    var complete_queries : live_query list

    proc init() : unit = {
      revealed_nodes <- fset0;
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

    proc challenge_live(
      member : principal,
      node : node_id
    ) : live_application_key option = {
      var result : live_application_key option;
      result <@ Core.challenge_live(member, node);
      return result;
    }

    (* Exact production reveal body with one removed conjunct:

         node \notin Core.challenged_live_nodes

       The secret, digest, production label, real KDF, prior-reveal exclusion,
       reveal mark, and complete query prefix are retained. *)
    proc reveal_live_key(
      member : principal,
      node : node_id
    ) : live_application_key option = {
      var secret_option : beekem_secret option;
      var digest_option : authorization_digest option;
      var label : live_key_label;
      var key : live_application_key;
      var result : live_application_key option;

      secret_option <- Core.member_secrets member node;
      digest_option <- Core.node_digests node;
      label <- witness;
      key <- witness;
      result <- None;
      complete_queries <- Core.queries;

      if (secret_option <> None /\ digest_option <> None /\
          node \notin revealed_nodes /\
          node \notin Core.revealed_live_nodes) {
        label <- live_label_of Core.public_state node (oget digest_option);
        key <@
          TestMultiDomainKeySchedule.derive_live(oget secret_option, label);
        revealed_nodes <- revealed_nodes `|` fset1 node;
        complete_queries <- rcons Core.queries
          {| lq_kind = LiveRevealQuery member;
             lq_operation = Some node |};
        result <- Some key;
      }

      return result;
    }
  }

  module A = ChallengeThenRevealMutationAdversary(MutatedOracle)

  proc main_with_fixed_bit(
    hidden_bit : bool
  ) : post_challenge_reveal_mutation_evidence = {
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
    MutatedOracle.init();

    A.attack();
    guess <@ A.guess();
    eligible <-
         live_trace_admissible
           1 Core.relation MutatedOracle.complete_queries Core.runtime_fault
      /\ ! Auth.unauthorized_accepted;
    win <- eligible /\ guess = hidden_bit;

    return
      {| pcre_hidden_bit = hidden_bit;
         pcre_eligible = eligible;
         pcre_guess = guess;
         pcre_challenge_returned = A.challenged <> None;
         pcre_reveal_returned = A.revealed <> None;
         pcre_challenge_count =
           challenge_query_count MutatedOracle.complete_queries;
         pcre_win = win |};
  }

  proc main() : bool = {
    var hidden_bit : bool;
    var evidence : post_challenge_reveal_mutation_evidence;

    hidden_bit <$ dbool;
    evidence <@ main_with_fixed_bit(hidden_bit);
    return evidence.`pcre_win;
  }
}.

lemma post_challenge_reveal_exclusion_removed_fixed_real :
  hoare [PostChallengeRevealExclusionRemovedGame.main_with_fixed_bit :
       arg = true
    ==>
       res.`pcre_win
    /\ res.`pcre_eligible
    /\ res.`pcre_guess
    /\ res.`pcre_challenge_returned
    /\ res.`pcre_reveal_returned
    /\ res.`pcre_challenge_count = 1].
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

lemma post_challenge_reveal_exclusion_removed_fixed_random :
  hoare [PostChallengeRevealExclusionRemovedGame.main_with_fixed_bit :
       arg = false
    ==>
       res.`pcre_win
    /\ res.`pcre_eligible
    /\ ! res.`pcre_guess
    /\ res.`pcre_challenge_returned
    /\ res.`pcre_reveal_returned
    /\ res.`pcre_challenge_count = 1].
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

lemma post_challenge_reveal_exclusion_removed_game_probability_one &m :
  Pr[PostChallengeRevealExclusionRemovedGame.main() @ &m : res] = 1%r.
proof.
  byphoare => //.
  proc.
  seq 1 : true 1%r 1%r 0%r 0%r.
  + rnd.
  + case (hidden_bit).
    + call post_challenge_reveal_exclusion_removed_fixed_real.
      auto.
    + call post_challenge_reveal_exclusion_removed_fixed_random.
      auto.
qed.

lemma post_challenge_reveal_exclusion_removed_normalized_advantage_half &m :
  mdprf_normalized_advantage
    (Pr[PostChallengeRevealExclusionRemovedGame.main() @ &m : res])
    1%r = 1%r / 2%r.
proof.
  rewrite post_challenge_reveal_exclusion_removed_game_probability_one.
  rewrite /mdprf_normalized_advantage.
  by smt().
qed.
