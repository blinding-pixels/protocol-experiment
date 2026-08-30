require import AllCore List FSet.
require import ProtocolTypes CanonicalEncoding LiveKeyGame.

(* Typed transcript of the multi-domain key schedule.  The constructors keep
   the live, history, and constrained-history domains disjoint in the logic;
   no string-label comparison or adversary-supplied domain bit is used. *)
type mdprf_live_input = {
  mpli_secret : beekem_secret;
  mpli_label : live_key_label
}.

type mdprf_history_input = {
  mphi_secret : beekem_secret;
  mphi_label : history_key_label
}.

type mdprf_history_capability_input = {
  mphci_secret : beekem_secret;
  mphci_label : history_key_label;
  mphci_cover : segment_cover
}.

type mdprf_query_kind = [
  | MdPrfLiveChallenge of mdprf_live_input
  | MdPrfHistoryQuery of mdprf_history_input
  | MdPrfHistoryCapabilityQuery of mdprf_history_capability_input
].

type mdprf_query = {
  mpq_kind : mdprf_query_kind
}.

op mdprf_kind_is_live (kind : mdprf_query_kind) : bool =
  with kind = MdPrfLiveChallenge input => true
  with kind = _ => false.

op mdprf_kind_is_history (kind : mdprf_query_kind) : bool =
  with kind = MdPrfHistoryQuery input => true
  with kind = _ => false.

op mdprf_kind_is_history_capability (kind : mdprf_query_kind) : bool =
  with kind = MdPrfHistoryCapabilityQuery input => true
  with kind = _ => false.

op mdprf_query_is_live (query : mdprf_query) : bool =
  mdprf_kind_is_live query.`mpq_kind.

op mdprf_query_is_history (query : mdprf_query) : bool =
  mdprf_kind_is_history query.`mpq_kind.

op mdprf_query_is_history_capability (query : mdprf_query) : bool =
  mdprf_kind_is_history_capability query.`mpq_kind.

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
  MdPrfLiveChallenge
    {| mpli_secret = secret; mpli_label = live_label |} <>
  MdPrfHistoryQuery
    {| mphi_secret = secret; mphi_label = history_label |}.
proof. by done. qed.

lemma mdprf_live_domain_is_not_history_capability_domain
    (secret : beekem_secret)
    (live_label : live_key_label)
    (history_label : history_key_label)
    (cover : segment_cover) :
  MdPrfLiveChallenge
    {| mpli_secret = secret; mpli_label = live_label |} <>
  MdPrfHistoryCapabilityQuery
    {| mphci_secret = secret;
       mphci_label = history_label;
       mphci_cover = cover |}.
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

type mdprf_adversary_result = {
  mpar_eligible : bool;
  mpar_guess : bool
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
