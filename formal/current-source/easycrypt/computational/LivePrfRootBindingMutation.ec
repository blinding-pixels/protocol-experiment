require import AllCore List FSet Distr.
require import ProtocolTypes ProtocolChecks CanonicalEncoding.
require import LiveKeyGame LivePrfTypes LivePrfGame.

(* Deliberate one-input KDF mutation: the live derivation binds every typed
   application label field but omits the BeeKEM root.  This control is kept at
   the primitive multi-domain PRF boundary because the authoritative BeeKEM
   root representation is still being developed on the parallel branch. *)
op root_mutation_reveal_secret : beekem_secret = BeeKemSecret 1300.
op root_mutation_challenge_secret : beekem_secret = BeeKemSecret 1301.

op root_mutation_label : live_key_label =
  {| lkl_protocol_version = expected_protocol_version;
     lkl_document_id = DocumentId 1302;
     lkl_node_id = NodeId 1303;
     lkl_authorization_digest = AuthorizationDigest 1304 |}.

lemma root_mutation_uses_distinct_roots_and_identical_labels :
     root_mutation_reveal_secret <> root_mutation_challenge_secret
  /\ root_mutation_label = root_mutation_label.
proof. by rewrite /root_mutation_reveal_secret /root_mutation_challenge_secret. qed.

op root_mutation_document_value (id : document_id) : int =
  with id = DocumentId value => value.

op root_mutation_node_value (id : node_id) : int =
  with id = NodeId value => value.

op root_mutation_digest_value (digest : authorization_digest) : int =
  with digest = ExactAuthorizationDigest state => 0
  with digest = AuthorizationDigest value => value
  with digest = InvalidAuthorizationDigest value => 0 - value.

op root_omitting_live_material (label : live_key_label) : int =
    label.`lkl_protocol_version
  + root_mutation_document_value label.`lkl_document_id
  + root_mutation_node_value label.`lkl_node_id
  + root_mutation_digest_value label.`lkl_authorization_digest.

op root_mutation_live_material (key : live_application_key) : int =
  with key = LiveApplicationKey material label => material.

op root_mutation_outputs_equal
    (left right : live_application_key) : bool =
  root_mutation_live_material left = root_mutation_live_material right.

module RootOmittingKeySchedule : MULTI_DOMAIN_KEY_SCHEDULE = {
  proc derive_live(
    secret : beekem_secret,
    label : live_key_label
  ) : live_application_key = {
    return LiveApplicationKey (root_omitting_live_material label) label;
  }

  proc derive_history(
    secret : beekem_secret,
    label : history_key_label
  ) : history_domain_output = {
    return HistoryDomainOutput (test_history_material secret label) label;
  }

  proc derive_history_capability(
    secret : beekem_secret,
    label : history_key_label,
    cover : segment_cover
  ) : history_capability_output = {
    return HistoryCapabilityOutput
      (test_history_material secret label) label cover;
  }
}.

(* A permitted live query and the distinguished live challenge use distinct
   roots under one identical label.  Omitting the root makes their real outputs
   equal, whereas the random challenge remains independent. *)
module RootBindingMutationAdversary(
  O : MULTI_DOMAIN_PRF_ORACLE
) = {
  proc attack(
    initial_state : protocol_state,
    initial_facts : signed_authorization_fact list,
    retention_kappa : int
  ) : mdprf_adversary_result = {
    var revealed : live_application_key;
    var challenged : live_application_key;
    var guess : bool;

    revealed <@ O.derive_live(
      root_mutation_reveal_secret,
      root_mutation_label
    );
    challenged <@ O.challenge_live(
      root_mutation_challenge_secret,
      root_mutation_label
    );
    guess <- root_mutation_outputs_equal revealed challenged;

    return {| mpar_eligible = true; mpar_guess = guess |};
  }
}.

module RootBindingMutationGame = MultiDomainPrfGame(
  RootBindingMutationAdversary,
  RootOmittingKeySchedule,
  TestLiveKeySampler
).

lemma root_omission_fixed_real :
  hoare [RootBindingMutationGame.main_with_fixed_bit :
       arg.`4 = true
    ==>
       res.`mpge_win
    /\ res.`mpge_eligible
    /\ res.`mpge_guess
    /\ res.`mpge_live_query_count = 1
    /\ res.`mpge_live_challenge_count = 1
    /\ res.`mpge_history_query_count = 0
    /\ res.`mpge_history_capability_query_count = 0].
proof.
  proc.
  inline *.
  auto.
  rewrite /root_mutation_outputs_equal /root_mutation_live_material
    /root_omitting_live_material /root_mutation_document_value
    /root_mutation_node_value /root_mutation_digest_value
    /root_mutation_reveal_secret /root_mutation_challenge_secret
    /root_mutation_label
    /mdprf_live_query_count /mdprf_live_challenge_count
    /mdprf_history_query_count
    /mdprf_history_capability_query_count
    /mdprf_query_is_live_query /mdprf_query_is_live_challenge
    /mdprf_query_is_history /mdprf_query_is_history_capability
    /mdprf_kind_is_live_query /mdprf_kind_is_live_challenge
    /mdprf_kind_is_history /mdprf_kind_is_history_capability /=.
  by smt().
qed.

lemma root_omission_fixed_random :
  hoare [RootBindingMutationGame.main_with_fixed_bit :
       arg.`4 = false
    ==>
       res.`mpge_win
    /\ res.`mpge_eligible
    /\ ! res.`mpge_guess
    /\ res.`mpge_live_query_count = 1
    /\ res.`mpge_live_challenge_count = 1
    /\ res.`mpge_history_query_count = 0
    /\ res.`mpge_history_capability_query_count = 0].
proof.
  proc.
  inline *.
  auto.
  rewrite /root_mutation_outputs_equal /root_mutation_live_material
    /root_omitting_live_material /root_mutation_document_value
    /root_mutation_node_value /root_mutation_digest_value
    /root_mutation_reveal_secret /root_mutation_challenge_secret
    /root_mutation_label
    /mdprf_live_query_count /mdprf_live_challenge_count
    /mdprf_history_query_count
    /mdprf_history_capability_query_count
    /mdprf_query_is_live_query /mdprf_query_is_live_challenge
    /mdprf_query_is_history /mdprf_query_is_history_capability
    /mdprf_kind_is_live_query /mdprf_kind_is_live_challenge
    /mdprf_kind_is_history /mdprf_kind_is_history_capability /=.
  by smt().
qed.

lemma root_omission_game_probability_one
    &m
    (initial_state : protocol_state)
    (initial_facts : signed_authorization_fact list)
    (retention_kappa : int) :
  Pr[
    RootBindingMutationGame.main(
      initial_state, initial_facts, retention_kappa
    ) @ &m : res
  ] = 1%r.
proof.
  byphoare => //.
  proc.
  inline RootBindingMutationGame.main_with_evidence.
  seq 1 : true 1%r 1%r 0%r 0%r.
  + rnd.
  + case (hidden_bit).
    + call root_omission_fixed_real.
      auto.
    + call root_omission_fixed_random.
      auto.
qed.

lemma root_omission_normalized_advantage_half
    &m
    (initial_state : protocol_state)
    (initial_facts : signed_authorization_fact list)
    (retention_kappa : int) :
  mdprf_normalized_advantage
    (Pr[
       RootBindingMutationGame.main(
         initial_state, initial_facts, retention_kappa
       ) @ &m : res
     ])
    1%r = 1%r / 2%r.
proof.
  rewrite root_omission_game_probability_one.
  rewrite /mdprf_normalized_advantage.
  by smt().
qed.
