require import AllCore List FSet Distr.
require import ProtocolTypes ProtocolChecks CanonicalEncoding.
require import LiveKeyGame LivePrfTypes LivePrfGame.

(* Deliberate one-field KDF mutation: the live derivation binds the BeeKEM
   root, document, node, and authorization digest, but omits the protocol
   version.  The typed transcript still records both complete labels. *)
op version_mutation_secret : beekem_secret = BeeKemSecret 1400.

op version_mutation_reveal_label : live_key_label =
  {| lkl_protocol_version = expected_protocol_version;
     lkl_document_id = DocumentId 1401;
     lkl_node_id = NodeId 1402;
     lkl_authorization_digest = AuthorizationDigest 1403 |}.

op version_mutation_challenge_label : live_key_label =
  {| lkl_protocol_version = expected_protocol_version + 1;
     lkl_document_id = DocumentId 1401;
     lkl_node_id = NodeId 1402;
     lkl_authorization_digest = AuthorizationDigest 1403 |}.

lemma version_mutation_labels_differ_only_in_protocol_version :
     version_mutation_reveal_label.`lkl_protocol_version <>
       version_mutation_challenge_label.`lkl_protocol_version
  /\ version_mutation_reveal_label.`lkl_document_id =
       version_mutation_challenge_label.`lkl_document_id
  /\ version_mutation_reveal_label.`lkl_node_id =
       version_mutation_challenge_label.`lkl_node_id
  /\ version_mutation_reveal_label.`lkl_authorization_digest =
       version_mutation_challenge_label.`lkl_authorization_digest.
proof.
  by rewrite /version_mutation_reveal_label
    /version_mutation_challenge_label /expected_protocol_version.
qed.

op version_mutation_document_value (id : document_id) : int =
  with id = DocumentId value => value.

op version_mutation_node_value (id : node_id) : int =
  with id = NodeId value => value.

op version_mutation_digest_value (digest : authorization_digest) : int =
  with digest = ExactAuthorizationDigest state => 0
  with digest = AuthorizationDigest value => value
  with digest = InvalidAuthorizationDigest value => 0 - value.

op version_omitting_live_material
    (secret : beekem_secret)
    (label : live_key_label) : int =
  with secret = BeeKemSecret value =>
       value
     + version_mutation_document_value label.`lkl_document_id
     + version_mutation_node_value label.`lkl_node_id
     + version_mutation_digest_value label.`lkl_authorization_digest.

op version_mutation_live_material (key : live_application_key) : int =
  with key = LiveApplicationKey material label => material.

op version_mutation_outputs_equal
    (left right : live_application_key) : bool =
  version_mutation_live_material left = version_mutation_live_material right.

module ProtocolVersionOmittingKeySchedule : MULTI_DOMAIN_KEY_SCHEDULE = {
  proc derive_live(
    secret : beekem_secret,
    label : live_key_label
  ) : live_application_key = {
    return LiveApplicationKey
      (version_omitting_live_material secret label) label;
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

module ProtocolVersionMutationAdversary(
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
      version_mutation_secret,
      version_mutation_reveal_label
    );
    challenged <@ O.challenge_live(
      version_mutation_secret,
      version_mutation_challenge_label
    );
    guess <- version_mutation_outputs_equal revealed challenged;

    return {| mpar_eligible = true; mpar_guess = guess |};
  }
}.

module ProtocolVersionMutationGame = MultiDomainPrfGame(
  ProtocolVersionMutationAdversary,
  ProtocolVersionOmittingKeySchedule,
  TestLiveKeySampler
).

lemma protocol_version_omission_fixed_real :
  hoare [ProtocolVersionMutationGame.main_with_fixed_bit :
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
  rewrite /version_mutation_outputs_equal /version_mutation_live_material
    /version_omitting_live_material /version_mutation_document_value
    /version_mutation_node_value /version_mutation_digest_value
    /version_mutation_secret /version_mutation_reveal_label
    /version_mutation_challenge_label /expected_protocol_version
    /mdprf_live_query_count /mdprf_live_challenge_count
    /mdprf_history_query_count
    /mdprf_history_capability_query_count
    /mdprf_query_is_live_query /mdprf_query_is_live_challenge
    /mdprf_query_is_history /mdprf_query_is_history_capability
    /mdprf_kind_is_live_query /mdprf_kind_is_live_challenge
    /mdprf_kind_is_history /mdprf_kind_is_history_capability /=.
  by smt().
qed.

lemma protocol_version_omission_fixed_random :
  hoare [ProtocolVersionMutationGame.main_with_fixed_bit :
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
  rewrite /version_mutation_outputs_equal /version_mutation_live_material
    /version_omitting_live_material /version_mutation_document_value
    /version_mutation_node_value /version_mutation_digest_value
    /version_mutation_secret /version_mutation_reveal_label
    /version_mutation_challenge_label /expected_protocol_version
    /mdprf_live_query_count /mdprf_live_challenge_count
    /mdprf_history_query_count
    /mdprf_history_capability_query_count
    /mdprf_query_is_live_query /mdprf_query_is_live_challenge
    /mdprf_query_is_history /mdprf_query_is_history_capability
    /mdprf_kind_is_live_query /mdprf_kind_is_live_challenge
    /mdprf_kind_is_history /mdprf_kind_is_history_capability /=.
  by smt().
qed.

lemma protocol_version_omission_game_probability_one
    &m
    (initial_state : protocol_state)
    (initial_facts : signed_authorization_fact list)
    (retention_kappa : int) :
  Pr[
    ProtocolVersionMutationGame.main(
      initial_state, initial_facts, retention_kappa
    ) @ &m : res
  ] = 1%r.
proof.
  byphoare => //.
  proc.
  inline ProtocolVersionMutationGame.main_with_evidence.
  seq 1 : true 1%r 1%r 0%r 0%r.
  + rnd.
  + case (hidden_bit).
    + call protocol_version_omission_fixed_real.
      auto.
    + call protocol_version_omission_fixed_random.
      auto.
qed.

lemma protocol_version_omission_normalized_advantage_half
    &m
    (initial_state : protocol_state)
    (initial_facts : signed_authorization_fact list)
    (retention_kappa : int) :
  mdprf_normalized_advantage
    (Pr[
       ProtocolVersionMutationGame.main(
         initial_state, initial_facts, retention_kappa
       ) @ &m : res
     ])
    1%r = 1%r / 2%r.
proof.
  rewrite protocol_version_omission_game_probability_one.
  rewrite /mdprf_normalized_advantage.
  by smt().
qed.
