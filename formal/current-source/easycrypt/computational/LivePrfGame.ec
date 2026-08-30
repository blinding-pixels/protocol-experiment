require import AllCore List Distr DBool.
require import ProtocolTypes CanonicalEncoding LiveKeyGame LivePrfTypes.

(* The primitive hidden bit changes only the distinguished live challenge.
   Permitted live reveals, history outputs, and constrained-history outputs are
   always answered by the same real multi-domain key schedule.  Every call is
   logged with its complete typed input. *)
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

  proc derive_live(
    secret : beekem_secret,
    label : live_key_label
  ) : live_application_key = {
    var answer : live_application_key;

    answer <@ K.derive_live(secret, label);
    queries <- rcons queries
      {| mpq_kind = MdPrfLiveQuery
           {| mpli_secret = secret; mpli_label = label |} |};
    return answer;
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
         mpge_live_query_count = mdprf_live_query_count O.queries;
         mpge_live_challenge_count = mdprf_live_challenge_count O.queries;
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

(* Fixed-bit distinguishing distance. *)
op mdprf_fixed_bit_advantage
    (real_one_probability random_one_probability : real) : real =
  if random_one_probability <= real_one_probability
  then real_one_probability - random_one_probability
  else random_one_probability - real_one_probability.

(* Success probability of the equivalent fair hidden-bit presentation when the
   real-bit event is [eligible /\ guess] and the random-bit event is
   [eligible /\ guess].  The random-bit win event is therefore the eligible
   mass not contained in the random-bit one-event. *)
op mdprf_hidden_bit_success
    (real_one_probability random_one_probability
     eligibility_probability : real) : real =
  (real_one_probability +
     (eligibility_probability - random_one_probability)) / 2%r.

(* Eligibility is challenger-computed and may have probability below one.  The
   fair baseline is therefore half the eligibility mass, not an unconditional
   one half. *)
op mdprf_normalized_advantage
    (success_probability eligibility_probability : real) : real =
  if eligibility_probability / 2%r <= success_probability
  then success_probability - eligibility_probability / 2%r
  else eligibility_probability / 2%r - success_probability.

lemma mdprf_hidden_bit_normalization
    (real_one_probability random_one_probability
     eligibility_probability : real) :
  mdprf_normalized_advantage
    (mdprf_hidden_bit_success
       real_one_probability random_one_probability eligibility_probability)
    eligibility_probability =
  mdprf_fixed_bit_advantage
    real_one_probability random_one_probability / 2%r.
proof.
  rewrite /mdprf_normalized_advantage /mdprf_hidden_bit_success
    /mdprf_fixed_bit_advantage.
  case (random_one_probability <= real_one_probability); smt().
qed.
