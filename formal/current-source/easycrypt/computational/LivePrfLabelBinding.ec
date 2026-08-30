require import AllCore FSet.
require import ProtocolTypes ProtocolChecks CanonicalEncoding.
require import LiveKeyGame LivePrfTypes.

(* Canonical application-to-PRF transcript constructors.  These operators add
   no cryptography and no admissibility condition; they package the exact typed
   inputs already consumed by [MultiDomainPrfOracle]. *)
op application_live_prf_input
    (secret : beekem_secret)
    (state : protocol_state)
    (node : node_id)
    (digest : authorization_digest) : mdprf_live_input =
  {| mpli_secret = secret;
     mpli_label = live_label_of state node digest |}.

op application_history_prf_input
    (secret : beekem_secret)
    (state : protocol_state)
    (segment : segment_id)
    (digest : authorization_digest) : mdprf_history_input =
  {| mphi_secret = secret;
     mphi_label = history_label_of state segment digest |}.

op application_history_capability_prf_input
    (secret : beekem_secret)
    (state : protocol_state)
    (segment : segment_id)
    (digest : authorization_digest)
    (cover : segment_cover) : mdprf_history_capability_input =
  {| mphci_secret = secret;
     mphci_label = history_label_of state segment digest;
     mphci_cover = cover |}.

op application_live_challenge_query
    (secret : beekem_secret)
    (state : protocol_state)
    (node : node_id)
    (digest : authorization_digest) : mdprf_query =
  {| mpq_kind =
       MdPrfLiveChallenge
         (application_live_prf_input secret state node digest) |}.

op application_history_query
    (secret : beekem_secret)
    (state : protocol_state)
    (segment : segment_id)
    (digest : authorization_digest) : mdprf_query =
  {| mpq_kind =
       MdPrfHistoryQuery
         (application_history_prf_input secret state segment digest) |}.

op application_history_capability_query
    (secret : beekem_secret)
    (state : protocol_state)
    (segment : segment_id)
    (digest : authorization_digest)
    (cover : segment_cover) : mdprf_query =
  {| mpq_kind =
       MdPrfHistoryCapabilityQuery
         (application_history_capability_prf_input
            secret state segment digest cover) |}.

lemma live_label_of_records_every_production_field
    (state : protocol_state)
    (node : node_id)
    (digest : authorization_digest) :
     (live_label_of state node digest).`lkl_protocol_version =
       expected_protocol_version
  /\ (live_label_of state node digest).`lkl_document_id =
       state.`ps_document_id
  /\ (live_label_of state node digest).`lkl_node_id = node
  /\ (live_label_of state node digest).`lkl_authorization_digest = digest.
proof. by rewrite /live_label_of. qed.

lemma history_label_of_records_every_production_field
    (state : protocol_state)
    (segment : segment_id)
    (digest : authorization_digest) :
     (history_label_of state segment digest).`hkl_protocol_version =
       expected_protocol_version
  /\ (history_label_of state segment digest).`hkl_document_id =
       state.`ps_document_id
  /\ (history_label_of state segment digest).`hkl_segment_id = segment
  /\ (history_label_of state segment digest).`hkl_authorization_digest = digest.
proof. by rewrite /history_label_of. qed.

(* Equality of distinguished live-challenge transcript entries exposes equality
   of every cryptographic input field.  In particular, a reduction cannot
   silently identify different roots, documents, nodes, or authorization
   digests while claiming to preserve the primitive query. *)
lemma application_live_challenge_query_injective
    (left_secret right_secret : beekem_secret)
    (left_state right_state : protocol_state)
    (left_node right_node : node_id)
    (left_digest right_digest : authorization_digest) :
  application_live_challenge_query
    left_secret left_state left_node left_digest =
  application_live_challenge_query
    right_secret right_state right_node right_digest =>
     left_secret = right_secret
  /\ left_state.`ps_document_id = right_state.`ps_document_id
  /\ left_node = right_node
  /\ left_digest = right_digest.
proof.
  rewrite /application_live_challenge_query /application_live_prf_input
    /live_label_of.
  by smt().
qed.

lemma application_history_query_injective
    (left_secret right_secret : beekem_secret)
    (left_state right_state : protocol_state)
    (left_segment right_segment : segment_id)
    (left_digest right_digest : authorization_digest) :
  application_history_query
    left_secret left_state left_segment left_digest =
  application_history_query
    right_secret right_state right_segment right_digest =>
     left_secret = right_secret
  /\ left_state.`ps_document_id = right_state.`ps_document_id
  /\ left_segment = right_segment
  /\ left_digest = right_digest.
proof.
  rewrite /application_history_query /application_history_prf_input
    /history_label_of.
  by smt().
qed.

lemma application_history_capability_query_injective
    (left_secret right_secret : beekem_secret)
    (left_state right_state : protocol_state)
    (left_segment right_segment : segment_id)
    (left_digest right_digest : authorization_digest)
    (left_cover right_cover : segment_cover) :
  application_history_capability_query
    left_secret left_state left_segment left_digest left_cover =
  application_history_capability_query
    right_secret right_state right_segment right_digest right_cover =>
     left_secret = right_secret
  /\ left_state.`ps_document_id = right_state.`ps_document_id
  /\ left_segment = right_segment
  /\ left_digest = right_digest
  /\ left_cover = right_cover.
proof.
  rewrite /application_history_capability_query
    /application_history_capability_prf_input /history_label_of.
  by smt().
qed.

lemma application_live_challenge_not_history_query
    (live_secret history_secret : beekem_secret)
    (live_state history_state : protocol_state)
    (node : node_id)
    (segment : segment_id)
    (live_digest history_digest : authorization_digest) :
  application_live_challenge_query
    live_secret live_state node live_digest <>
  application_history_query
    history_secret history_state segment history_digest.
proof.
  by rewrite /application_live_challenge_query /application_history_query.
qed.

lemma application_live_challenge_not_history_capability_query
    (live_secret history_secret : beekem_secret)
    (live_state history_state : protocol_state)
    (node : node_id)
    (segment : segment_id)
    (live_digest history_digest : authorization_digest)
    (cover : segment_cover) :
  application_live_challenge_query
    live_secret live_state node live_digest <>
  application_history_capability_query
    history_secret history_state segment history_digest cover.
proof.
  by rewrite /application_live_challenge_query
    /application_history_capability_query.
qed.
