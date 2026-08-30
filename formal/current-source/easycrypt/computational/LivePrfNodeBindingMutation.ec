require import AllCore List FSet Distr.
require import ProtocolTypes ProtocolChecks CanonicalEncoding.
require import LiveKeyGame LivePrfTypes LivePrfGame.

(* Deliberate one-field KDF mutation: the live derivation binds the BeeKEM
   root, protocol version, document identifier, and authorization digest, but
   omits the node identifier.  The typed transcript still records both complete
   labels, so the mutation changes only the cryptographic derivation. *)
op node_mutation_secret : beekem_secret = BeeKemSecret 1600.

op node_mutation_reveal_label : live_key_label =
  {| lkl_protocol_version = expected_protocol_version;
     lkl_document_id = DocumentId 1601;
     lkl_node_id = NodeId 1602;
     lkl_authorization_digest = AuthorizationDigest 1603 |}.

op node_mutation_challenge_label : live_key_label =
  {| lkl_protocol_version = expected_protocol_version;
     lkl_document_id = DocumentId 1601;
     lkl_node_id = NodeId 1604;
     lkl_authorization_digest = AuthorizationDigest 1603 |}.

lemma node_mutation_labels_differ_only_in_node_id :
     node_mutation_reveal_label.`lkl_protocol_version =
       node_mutation_challenge_label.`lkl_protocol_version
  /\ node_mutation_reveal_label.`lkl_document_id =
       node_mutation_challenge_label.`lkl_document_id
  /\ node_mutation_reveal_label.`lkl_node_id <>
       node_mutation_challenge_label.`lkl_node_id
  /\ node_mutation_reveal_label.`lkl_authorization_digest =
       node_mutation_challenge_label.`lkl_authorization_digest.
proof.
  by rewrite /node_mutation_reveal_label /node_mutation_challenge_label.
qed.

op node_mutation_document_value (id : document_id) : int =
  with id = DocumentId value => value.

op node_mutation_digest_value (digest : authorization_digest) : int =
  with digest = ExactAuthorizationDigest state => 0
  with digest = AuthorizationDigest value => value
  with digest = InvalidAuthorizationDigest value => 0 - value.

op node_omitting_live_material
    (secret : beekem_secret)
    (label : live_key_label) : int =
  with secret = BeeKemSecret value =>
       value
     + label.`lkl_protocol_version
     + node_mutation_document_value label.`lkl_document_id
     + node_mutation_digest_value label.`lkl_authorization_digest.

op node_mutation_live_material (key : live_application_key) : int =
  with key = LiveApplicationKey material label => material.

op node_mutation_outputs_equal
    (left right : live_application_key) : bool =
  node_mutation_live_material left = node_mutation_live_material right.

module NodeOmittingKeySchedule : MULTI_DOMAIN_KEY_SCHEDULE = {
  proc derive_live(
    secret : beekem_secret,
    label : live_key_label
  ) : live_application_key = {
    return LiveApplicationKey (node_omitting_live_material secret label) label;
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

module NodeBindingMutationAdversary(
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

    revealed <@ O.derive_live(node_mutation_secret, node_mutation_reveal_label);
    challenged <@ O.challenge_live(
      node_mutation_secret, node_mutation_challenge_label
    );
    guess <- node_mutation_outputs_equal revealed challenged;

    return {| mpar_eligible = true; mpar_guess = guess |};
  }
}.

module NodeBindingMutationGame = MultiDomainPrfGame(
  NodeBindingMutationAdversary,
  NodeOmittingKeySchedule,
  TestLiveKeySampler
).

lemma node_id_omission_fixed_real :
  hoare [NodeBindingMutationGame.main_with_fixed_bit :
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
  rewrite /node_mutation_outputs_equal /node_mutation_live_material
    /node_omitting_live_material /node_mutation_document_value
    /node_mutation_digest_value /node_mutation_secret
    /node_mutation_reveal_label /node_mutation_challenge_label
    /expected_protocol_version
    /mdprf_live_query_count /mdprf_live_challenge_count
    /mdprf_history_query_count /mdprf_history_capability_query_count
    /mdprf_query_is_live_query /mdprf_query_is_live_challenge
    /mdprf_query_is_history /mdprf_query_is_history_capability
    /mdprf_kind_is_live_query /mdprf_kind_is_live_challenge
    /mdprf_kind_is_history /mdprf_kind_is_history_capability /=.
  by smt().
qed.

lemma node_id_omission_fixed_random :
  hoare [NodeBindingMutationGame.main_with_fixed_bit :
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
  rewrite /node_mutation_outputs_equal /node_mutation_live_material
    /node_omitting_live_material /node_mutation_document_value
    /node_mutation_digest_value /node_mutation_secret
    /node_mutation_reveal_label /node_mutation_challenge_label
    /expected_protocol_version
    /mdprf_live_query_count /mdprf_live_challenge_count
    /mdprf_history_query_count /mdprf_history_capability_query_count
    /mdprf_query_is_live_query /mdprf_query_is_live_challenge
    /mdprf_query_is_history /mdprf_query_is_history_capability
    /mdprf_kind_is_live_query /mdprf_kind_is_live_challenge
    /mdprf_kind_is_history /mdprf_kind_is_history_capability /=.
  by smt().
qed.

lemma node_id_omission_game_probability_one
    &m
    (initial_state : protocol_state)
    (initial_facts : signed_authorization_fact list)
    (retention_kappa : int) :
  Pr[
    NodeBindingMutationGame.main(
      initial_state, initial_facts, retention_kappa
    ) @ &m : res
  ] = 1%r.
proof.
  byphoare => //.
  proc.
  inline NodeBindingMutationGame.main_with_evidence.
  seq 1 : true 1%r 1%r 0%r 0%r.
  + rnd.
  + case (hidden_bit).
    + call node_id_omission_fixed_real.
      auto.
    + call node_id_omission_fixed_random.
      auto.
qed.

lemma node_id_omission_normalized_advantage_half
    &m
    (initial_state : protocol_state)
    (initial_facts : signed_authorization_fact list)
    (retention_kappa : int) :
  mdprf_normalized_advantage
    (Pr[
       NodeBindingMutationGame.main(
         initial_state, initial_facts, retention_kappa
       ) @ &m : res
     ])
    1%r = 1%r / 2%r.
proof.
  rewrite node_id_omission_game_probability_one.
  rewrite /mdprf_normalized_advantage.
  by smt().
qed.
