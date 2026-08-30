require import AllCore List FSet Distr.
require import ProtocolTypes ProtocolChecks CanonicalEncoding.
require import LiveKeyGame LivePrfTypes LivePrfGame.

(* Deliberate one-field KDF mutation: the live derivation binds the secret,
   protocol version, document, and node, but omits the authorization digest.
   The typed transcript still records both complete labels.  This is a
   counterexample control showing that merely logging the digest is not enough;
   the production PRF input must cryptographically bind it. *)
op digest_mutation_secret : beekem_secret = BeeKemSecret 1200.

op digest_mutation_reveal_label : live_key_label =
  {| lkl_protocol_version = expected_protocol_version;
     lkl_document_id = DocumentId 1201;
     lkl_node_id = NodeId 1202;
     lkl_authorization_digest = AuthorizationDigest 1203 |}.

op digest_mutation_challenge_label : live_key_label =
  {| lkl_protocol_version = expected_protocol_version;
     lkl_document_id = DocumentId 1201;
     lkl_node_id = NodeId 1202;
     lkl_authorization_digest = AuthorizationDigest 1204 |}.

lemma digest_mutation_labels_differ_only_in_authorization_digest :
     digest_mutation_reveal_label.`lkl_protocol_version =
       digest_mutation_challenge_label.`lkl_protocol_version
  /\ digest_mutation_reveal_label.`lkl_document_id =
       digest_mutation_challenge_label.`lkl_document_id
  /\ digest_mutation_reveal_label.`lkl_node_id =
       digest_mutation_challenge_label.`lkl_node_id
  /\ digest_mutation_reveal_label.`lkl_authorization_digest <>
       digest_mutation_challenge_label.`lkl_authorization_digest.
proof.
  by rewrite /digest_mutation_reveal_label
    /digest_mutation_challenge_label.
qed.

op digest_mutation_document_value (id : document_id) : int =
  with id = DocumentId value => value.

op digest_mutation_node_value (id : node_id) : int =
  with id = NodeId value => value.

op digest_omitting_live_material
    (secret : beekem_secret)
    (label : live_key_label) : int =
  with secret = BeeKemSecret value =>
       value
     + label.`lkl_protocol_version
     + digest_mutation_document_value label.`lkl_document_id
     + digest_mutation_node_value label.`lkl_node_id.

op digest_mutation_live_material (key : live_application_key) : int =
  with key = LiveApplicationKey material label => material.

op digest_mutation_outputs_equal
    (left right : live_application_key) : bool =
  digest_mutation_live_material left = digest_mutation_live_material right.

module AuthorizationDigestOmittingKeySchedule : MULTI_DOMAIN_KEY_SCHEDULE = {
  proc derive_live(
    secret : beekem_secret,
    label : live_key_label
  ) : live_application_key = {
    return LiveApplicationKey
      (digest_omitting_live_material secret label) label;
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

(* A permitted live query uses one authorization digest and the distinguished
   live challenge uses another while every other input field, including the
   root, is identical.  If the KDF omits the digest, equality of the two public
   key materials distinguishes the real and random challenge branches. *)
module AuthorizationDigestMutationAdversary(
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
      digest_mutation_secret,
      digest_mutation_reveal_label
    );
    challenged <@ O.challenge_live(
      digest_mutation_secret,
      digest_mutation_challenge_label
    );
    guess <- digest_mutation_outputs_equal revealed challenged;

    return {| mpar_eligible = true; mpar_guess = guess |};
  }
}.

module AuthorizationDigestMutationGame = MultiDomainPrfGame(
  AuthorizationDigestMutationAdversary,
  AuthorizationDigestOmittingKeySchedule,
  TestLiveKeySampler
).

lemma authorization_digest_omission_fixed_real :
  hoare [AuthorizationDigestMutationGame.main_with_fixed_bit :
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
  rewrite /digest_mutation_outputs_equal /digest_mutation_live_material
    /digest_omitting_live_material /digest_mutation_document_value
    /digest_mutation_node_value /digest_mutation_secret
    /digest_mutation_reveal_label /digest_mutation_challenge_label
    /mdprf_live_query_count /mdprf_live_challenge_count
    /mdprf_history_query_count
    /mdprf_history_capability_query_count
    /mdprf_query_is_live_query /mdprf_query_is_live_challenge
    /mdprf_query_is_history /mdprf_query_is_history_capability
    /mdprf_kind_is_live_query /mdprf_kind_is_live_challenge
    /mdprf_kind_is_history /mdprf_kind_is_history_capability /=.
  by smt().
qed.

lemma authorization_digest_omission_fixed_random :
  hoare [AuthorizationDigestMutationGame.main_with_fixed_bit :
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
  rewrite /digest_mutation_outputs_equal /digest_mutation_live_material
    /digest_omitting_live_material /digest_mutation_document_value
    /digest_mutation_node_value /digest_mutation_secret
    /digest_mutation_reveal_label /digest_mutation_challenge_label
    /mdprf_live_query_count /mdprf_live_challenge_count
    /mdprf_history_query_count
    /mdprf_history_capability_query_count
    /mdprf_query_is_live_query /mdprf_query_is_live_challenge
    /mdprf_query_is_history /mdprf_query_is_history_capability
    /mdprf_kind_is_live_query /mdprf_kind_is_live_challenge
    /mdprf_kind_is_history /mdprf_kind_is_history_capability /=.
  by smt().
qed.

lemma authorization_digest_omission_game_probability_one
    &m
    (initial_state : protocol_state)
    (initial_facts : signed_authorization_fact list)
    (retention_kappa : int) :
  Pr[
    AuthorizationDigestMutationGame.main(
      initial_state, initial_facts, retention_kappa
    ) @ &m : res
  ] = 1%r.
proof.
  byphoare => //.
  proc.
  inline AuthorizationDigestMutationGame.main_with_evidence.
  seq 1 : true 1%r 1%r 0%r 0%r.
  + rnd.
  + case (hidden_bit).
    + call authorization_digest_omission_fixed_real.
      auto.
    + call authorization_digest_omission_fixed_random.
      auto.
qed.

lemma authorization_digest_omission_normalized_advantage_half
    &m
    (initial_state : protocol_state)
    (initial_facts : signed_authorization_fact list)
    (retention_kappa : int) :
  mdprf_normalized_advantage
    (Pr[
       AuthorizationDigestMutationGame.main(
         initial_state, initial_facts, retention_kappa
       ) @ &m : res
     ])
    1%r = 1%r / 2%r.
proof.
  rewrite authorization_digest_omission_game_probability_one.
  rewrite /mdprf_normalized_advantage.
  by smt().
qed.
