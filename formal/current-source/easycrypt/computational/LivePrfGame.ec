require import AllCore List Distr DBool.
require import ProtocolTypes CanonicalEncoding LiveKeyGame LivePrfTypes.

(* The primitive hidden bit changes only the live domain.  Permitted history
   and constrained-capability queries are always answered by the same real
   multi-domain key schedule and are logged with their complete typed input. *)
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
      {| mpq_kind = MdPrfLiveChallenge
           {| mpli_secret = secret; mpli_label = label |} |};
    return answer;
  }

  proc derive_history(
    secret : beekem_secret,
    label : history_key_label
  ) : history_domain_output = {
    var answer : history_domain_output;

    answer <@ K.derive_history(secret, label);
    queries <- rcons queries
      {| mpq_kind = MdPrfHistoryQuery
           {| mphi_secret = secret; mphi_label = label |} |};
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
      {| mpq_kind = MdPrfHistoryCapabilityQuery
           {| mphci_secret = secret;
              mphci_label = label;
              mphci_cover = cover |} |};
    return answer;
  }
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
