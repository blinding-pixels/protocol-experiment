require import AllCore List FSet Distr DBool.
require import ProtocolTypes CanonicalEncoding ProtocolPrimitives AuthorizationState.
require import AuthorizationAncestry UnauthorizedSignatureReduction UnauthorizedOriginGame.
require import LiveKeyGame.

import PG.

(* ------------------------------------------------------------------------- *)
(* Deliverable L, application multi-domain PRF reduction.                     *)
(*                                                                           *)
(* This file is intentionally independent of the provisional BeeKEM game.     *)
(* [B] is the L2 BeeKEM-backed runtime supplied by the surrounding hybrid.     *)
(* The only BeeKEM-sensitive value crossing this boundary is the root passed   *)
(* to the production key schedule.  When the authoritative BeeKEM interface   *)
(* is merged, its application adapter can replace [B] without changing this   *)
(* primitive game, reduction adversary, history simulation, or ideal game.     *)
(* ------------------------------------------------------------------------- *)

type mdprf_query_kind = [
  | MdPrfLiveChallenge of beekem_secret & live_key_label
  | MdPrfHistoryQuery of beekem_secret & history_key_label
  | MdPrfHistoryCapabilityQuery of
      beekem_secret & history_key_label & segment_cover
].

type mdprf_query = {
  mpq_kind : mdprf_query_kind
}.

op mdprf_query_is_live (query : mdprf_query) : bool =
  with query.`mpq_kind = MdPrfLiveChallenge secret label => true
  with query.`mpq_kind = _ => false.

op mdprf_query_is_history (query : mdprf_query) : bool =
  with query.`mpq_kind = MdPrfHistoryQuery secret label => true
  with query.`mpq_kind = _ => false.

op mdprf_query_is_history_capability (query : mdprf_query) : bool =
  with query.`mpq_kind =
    MdPrfHistoryCapabilityQuery secret label cover => true
  with query.`mpq_kind = _ => false.

op mdprf_live_query_count (queries : mdprf_query list) : int =
  with queries = [] => 0
  with queries = query :: rest =>
    (if mdprf_query_is_live query then 1 else 0) +
    mdprf_live_query_count rest.

op mdprf_history_query_count (queries : mdprf_query list) : int =
  with queries = [] => 0
  with queries = query :: rest =>
    (if mdprf_query_is_history query then 1 else 0) +
    mdprf_history_query_count rest.

op mdprf_history_capability_query_count
    (queries : mdprf_query list) : int =
  with queries = [] => 0
  with queries = query :: rest =>
    (if mdprf_query_is_history_capability query then 1 else 0) +
    mdprf_history_capability_query_count rest.

lemma mdprf_live_domain_is_not_history_domain
    (secret : beekem_secret)
    (live_label : live_key_label)
    (history_label : history_key_label) :
  MdPrfLiveChallenge secret live_label <>
  MdPrfHistoryQuery secret history_label.
proof. by done. qed.

lemma mdprf_live_domain_is_not_history_capability_domain
    (secret : beekem_secret)
    (live_label : live_key_label)
    (history_label : history_key_label)
    (cover : segment_cover) :
  MdPrfLiveChallenge secret live_label <>
  MdPrfHistoryCapabilityQuery secret history_label cover.
proof. by done. qed.

module type MULTI_DOMAIN_PRF_ORACLE = {
  proc challenge_live(
    secret : beekem_secret,
    label : live_key_label
  ) : live_application_key

  proc derive_history(
    secret : beekem_secret,
    label : history_key_label
  ) : history_domain_output

  proc derive_history_capability(
    secret : beekem_secret,
    label : history_key_label,
    cover : segment_cover
  ) : history_capability_output
}.

(* The primitive challenge bit changes only the live domain.  Every permitted
   history and constrained-capability query is answered by the same real
   multi-domain schedule and is logged with its complete typed input. *)
module MultiDomainPrfOracle(
  K : MULTI_DOMAIN_KEY_SCHEDULE,
  R : LIVE_KEY_SAMPLER
) = {
  var hidden_bit : bool
  var queries : mdprf_query list

  proc init(bit : bool) : unit = {
    hidden_bit <- bit;
    queries <- [];
  }

  proc challenge_live(
    secret : beekem_secret,
    label : live_key_label
  ) : live_application_key = {
    var real_key : live_application_key;
    var random_key : live_application_key;
    var answer : live_application_key;

    real_key <@ K.derive_live(secret, label);
    random_key <@ R.sample(label);
    answer <- if hidden_bit then real_key else random_key;
    queries <- rcons queries
      {| mpq_kind = MdPrfLiveChallenge secret label |};
    return answer;
  }

  proc derive_history(
    secret : beekem_secret,
    label : history_key_label
  ) : history_domain_output = {
    var answer : history_domain_output;

    answer <@ K.derive_history(secret, label);
    queries <- rcons queries
      {| mpq_kind = MdPrfHistoryQuery secret label |};
    return answer;
  }

  proc derive_history_capability(
    secret : beekem_secret,
    label : history_key_label,
    cover : segment_cover
  ) : history_capability_output = {
    var answer : history_capability_output;

    answer <@ K.derive_history_capability(secret, label, cover);
    queries <- rcons queries
      {| mpq_kind =
           MdPrfHistoryCapabilityQuery secret label cover |};
    return answer;
  }
}.

type mdprf_adversary_result = {
  mpar_eligible : bool;
  mpar_guess : bool
}.

module type MULTI_DOMAIN_PRF_ADVERSARY(
  O : MULTI_DOMAIN_PRF_ORACLE
) = {
  proc attack(
    initial_state : protocol_state,
    initial_facts : signed_authorization_fact list,
    retention_kappa : int
  ) : mdprf_adversary_result
}.

type mdprf_game_evidence = {
  mpge_hidden_bit : bool;
  mpge_eligible : bool;
  mpge_guess : bool;
  mpge_live_challenge_count : int;
  mpge_history_query_count : int;
  mpge_history_capability_query_count : int;
  mpge_win : bool
}.

module MultiDomainPrfGame(
  A : MULTI_DOMAIN_PRF_ADVERSARY,
  K : MULTI_DOMAIN_KEY_SCHEDULE,
  R : LIVE_KEY_SAMPLER
) = {
  module O = MultiDomainPrfOracle(K, R)
  module A = A(O)

  var last_evidence : mdprf_game_evidence

  proc main_with_fixed_bit(
    initial_state : protocol_state,
    initial_facts : signed_authorization_fact list,
    retention_kappa : int,
    hidden_bit : bool
  ) : mdprf_game_evidence = {
    var result : mdprf_adversary_result;
    var win : bool;

    O.init(hidden_bit);
    result <@ A.attack(initial_state, initial_facts, retention_kappa);
    win <- result.`mpar_eligible /\ result.`mpar_guess = hidden_bit;

    last_evidence <-
      {| mpge_hidden_bit = hidden_bit;
         mpge_eligible = result.`mpar_eligible;
         mpge_guess = result.`mpar_guess;
         mpge_live_challenge_count = mdprf_live_query_count O.queries;
         mpge_history_query_count = mdprf_history_query_count O.queries;
         mpge_history_capability_query_count =
           mdprf_history_capability_query_count O.queries;
         mpge_win = win |};
    return last_evidence;
  }

  proc main_with_evidence(
    initial_state : protocol_state,
    initial_facts : signed_authorization_fact list,
    retention_kappa : int
  ) : mdprf_game_evidence = {
    var hidden_bit : bool;
    var evidence : mdprf_game_evidence;

    hidden_bit <$ dbool;
    evidence <@ main_with_fixed_bit(
      initial_state, initial_facts, retention_kappa, hidden_bit
    );
    return evidence;
  }

  proc main(
    initial_state : protocol_state,
    initial_facts : signed_authorization_fact list,
    retention_kappa : int
  ) : bool = {
    var evidence : mdprf_game_evidence;

    evidence <@ main_with_evidence(
      initial_state, initial_facts, retention_kappa
    );
    return evidence.`mpge_win;
  }
}.

op mdprf_normalized_advantage (success_probability : real) : real =
  if 1%r / 2%r <= success_probability
  then success_probability - 1%r / 2%r
  else 1%r / 2%r - success_probability.

(* This adapter is the reduction's only key-schedule implementation.  The
   application core still constructs every exact production label.  Live calls
   reach the primitive challenge; history calls are forwarded to the permitted
   real-domain oracles. *)
module PrfOracleBackedKeySchedule(
  O : MULTI_DOMAIN_PRF_ORACLE
) : MULTI_DOMAIN_KEY_SCHEDULE = {
  proc derive_live(
    secret : beekem_secret,
    label : live_key_label
  ) : live_application_key = {
    var answer : live_application_key;
    answer <@ O.challenge_live(secret, label);
    return answer;
  }

  proc derive_history(
    secret : beekem_secret,
    label : history_key_label
  ) : history_domain_output = {
    var answer : history_domain_output;
    answer <@ O.derive_history(secret, label);
    return answer;
  }

  proc derive_history_capability(
    secret : beekem_secret,
    label : history_key_label,
    cover : segment_cover
  ) : history_capability_output = {
    var answer : history_capability_output;
    answer <@ O.derive_history_capability(secret, label, cover);
    return answer;
  }
}.

(* [LiveProtocolCore.challenge_live] evaluates both branches before selecting
   one.  The reduction fixes that application selector to the real branch, so
   this deterministic sampler is called but its result is never returned. *)
module PrfReductionUnusedSampler : LIVE_KEY_SAMPLER = {
  proc sample(label : live_key_label) : live_application_key = {
    return LiveApplicationKey 0 label;
  }
}.

(* Concrete BPRFLive reduction.  It executes the full origin-aware application
   environment.  Its eligibility gate is challenger-computed and includes the
   authenticated L1 event.  The current [live_trace_admissible] call is the
   explicit provisional BeeKEM adapter seam; the PRF simulation itself does not
   inspect or reconstruct BeeKEM safety. *)
module BPRFLive(
  A : LIVE_KEY_ADVERSARY,
  S : SIGNATURE_SCHEME,
  H : NODE_HASH,
  B : BEEKEM_LIVE_RUNTIME
)(O : MULTI_DOMAIN_PRF_ORACLE) = {
  module SO = PG.LoggedSignatureOracle(S)
  module Auth = OriginTrackedCandidateEnvironment(SO, H)
  module K = PrfOracleBackedKeySchedule(O)
  module Live = LiveProtocolCore(Auth, B, K, PrfReductionUnusedSampler)
  module A = A(Live)

  proc attack(
    initial_state : protocol_state,
    initial_facts : signed_authorization_fact list,
    retention_kappa : int
  ) : mdprf_adversary_result = {
    var initial_authorization : authorization_state option;
    var initial_digest : authorization_digest;
    var adversary_guess : bool;
    var eligible : bool;

    initial_authorization <-
      live_initial_authorization initial_state initial_facts;
    initial_digest <-
      live_initial_authorization_digest initial_state initial_facts;
    adversary_guess <- false;
    eligible <- false;

    SO.init();
    Auth.init(initial_state);
    Live.init(initial_state, retention_kappa, true, initial_digest);
    A.attack();
    adversary_guess <@ A.guess();

    eligible <-
         initial_authorization <> None
      /\ live_trace_admissible
           retention_kappa Live.relation Live.queries Live.runtime_fault
      /\ ! Auth.unauthorized_accepted;

    return
      {| mpar_eligible = eligible;
         mpar_guess = adversary_guess |};
  }
}.

(* ------------------------------------------------------------------------- *)
(* Checker-backed non-vacuity and insecure-KDF control.                       *)
(* ------------------------------------------------------------------------- *)

op prf_control_creator : principal =
  {| p_verification_key = VerificationKey 901;
     p_incarnation_nonce = IncarnationNonce 902 |}.

op prf_control_state : protocol_state =
  {| ps_creator = prf_control_creator;
     ps_document_id = DocumentId 903;
     ps_nodes = fset0;
     ps_closures = fun _ => None;
     ps_fact_contents = fun _ => None;
     ps_seen_operation_ids = fset0;
     ps_seen_nonces = fset0;
     ps_beekem_paths = fun _ => None;
     ps_history_expectation = None;
     ps_expected_puncture_regions = fset0 |}.

op prf_control_key_guesses_real (key : live_application_key) : bool =
  with key = LiveApplicationKey material label => 0 <= material.

module PrfControlApplicationAdversary(
  O : LIVE_PROTOCOL_ORACLE
) = {
  var guessed_bit : bool

  proc attack() : unit = {
    var created : node_id option;
    var updated : node_id option;
    var history : history_domain_output option;
    var capability : history_capability_output option;
    var challenge : live_application_key option;

    guessed_bit <- false;
    created <@ O.create_group(prf_control_creator, fset0);
    updated <@ O.send_beekem_update(prf_control_creator);
    history <@ O.reveal_history_output(
      prf_control_creator, NodeId 2, SegmentId 904
    );
    capability <@ O.reveal_history_capability(
      prf_control_creator, NodeId 2, SegmentId 904, fset0
    );
    challenge <@ O.challenge_live(prf_control_creator, NodeId 2);
    if (challenge <> None) {
      guessed_bit <- prf_control_key_guesses_real (oget challenge);
    }
  }

  proc guess() : bool = {
    return guessed_bit;
  }
}.

module PrfControlGame = MultiDomainPrfGame(
  BPRFLive(
    PrfControlApplicationAdversary,
    TestSignature,
    TestNodeHash,
    TestBeeKemLiveRuntime
  ),
  TestMultiDomainKeySchedule,
  TestLiveKeySampler
).

lemma bprf_live_fixed_real_control :
  hoare [PrfControlGame.main_with_fixed_bit :
    arg = (prf_control_state, [], 1, true) ==>
       res.`mpge_win
    /\ res.`mpge_eligible
    /\ res.`mpge_guess
    /\ res.`mpge_live_challenge_count = 1
    /\ res.`mpge_history_query_count = 1
    /\ res.`mpge_history_capability_query_count = 1].
proof.
  proc.
  inline *.
  auto.
  rewrite /prf_control_state /prf_control_creator
    /prf_control_key_guesses_real
    /live_initial_authorization /live_initial_authorization_digest
    /authorization_policy_replay /authorization_policy_replay_from
    /empty_active_member_store /active_member_store_put
    /active_member_store_of_set
    /empty_control_store /empty_node_digest_store
    /empty_delivery_store /empty_member_secret_store
    /empty_member_head_store /empty_causal_relation
    /control_store_put /node_digest_store_put
    /delivery_store_put /member_secret_store_put
    /member_head_store_put /node_after /test_secret_for_node
    /history_label_of /live_label_of
    /test_history_material /test_live_material
    /all_nodes_known /all_nodes_known_list
    /all_predecessors_delivered /all_predecessors_delivered_list
    /causal_relation_extend /predecessor_reaches_list
    /challenge_query_count /query_is_challenge
    /live_trace_admissible /bee_safe_kappa
    /every_challenge_safe /query_challenge_member
    /every_compromise_safe_for_challenge /query_compromise_member
    /mdprf_live_query_count /mdprf_history_query_count
    /mdprf_history_capability_query_count
    /mdprf_query_is_live /mdprf_query_is_history
    /mdprf_query_is_history_capability /=.
  by rewrite !inE; smt().
qed.

lemma bprf_live_fixed_random_control :
  hoare [PrfControlGame.main_with_fixed_bit :
    arg = (prf_control_state, [], 1, false) ==>
       res.`mpge_win
    /\ res.`mpge_eligible
    /\ ! res.`mpge_guess
    /\ res.`mpge_live_challenge_count = 1
    /\ res.`mpge_history_query_count = 1
    /\ res.`mpge_history_capability_query_count = 1].
proof.
  proc.
  inline *.
  auto.
  rewrite /prf_control_state /prf_control_creator
    /prf_control_key_guesses_real
    /live_initial_authorization /live_initial_authorization_digest
    /authorization_policy_replay /authorization_policy_replay_from
    /empty_active_member_store /active_member_store_put
    /active_member_store_of_set
    /empty_control_store /empty_node_digest_store
    /empty_delivery_store /empty_member_secret_store
    /empty_member_head_store /empty_causal_relation
    /control_store_put /node_digest_store_put
    /delivery_store_put /member_secret_store_put
    /member_head_store_put /node_after /test_secret_for_node
    /history_label_of /live_label_of
    /test_history_material /test_live_material
    /all_nodes_known /all_nodes_known_list
    /all_predecessors_delivered /all_predecessors_delivered_list
    /causal_relation_extend /predecessor_reaches_list
    /challenge_query_count /query_is_challenge
    /live_trace_admissible /bee_safe_kappa
    /every_challenge_safe /query_challenge_member
    /every_compromise_safe_for_challenge /query_compromise_member
    /mdprf_live_query_count /mdprf_history_query_count
    /mdprf_history_capability_query_count
    /mdprf_query_is_live /mdprf_query_is_history
    /mdprf_query_is_history_capability /=.
  by rewrite !inE; smt().
qed.

lemma insecure_test_kdf_prf_game_probability_one &m :
  Pr[
    PrfControlGame.main(prf_control_state, [], 1) @ &m : res
  ] = 1%r.
proof.
  byphoare => //.
  proc.
  inline PrfControlGame.main_with_evidence.
  seq 1 : true 1%r 1%r 0%r 0%r.
  + rnd.
  + case (hidden_bit).
    + call bprf_live_fixed_real_control.
      auto.
    + call bprf_live_fixed_random_control.
      auto.
qed.

lemma insecure_test_kdf_prf_normalized_advantage_half &m :
  mdprf_normalized_advantage
    (Pr[
       PrfControlGame.main(prf_control_state, [], 1) @ &m : res
     ]) = 1%r / 2%r.
proof.
  rewrite insecure_test_kdf_prf_game_probability_one.
  rewrite /mdprf_normalized_advantage.
  by norm.
qed.
