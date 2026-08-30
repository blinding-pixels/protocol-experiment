require import AllCore List DBool.
require import BeeKemTypes BeeKemKiGame.

(* -------------------------------------------------------------------- *)
(* NIKE HKR-CKS.  This is the exact oracle surface used by the BeeKEM
   Appendix-B reduction: adaptive registration of honestly generated public
   keys and adaptive tests on pairs of registered users under one hidden bit.
   The adversary never receives the registered secret keys. *)

module type BEEKEM_NIKE = {
  proc keygen() : beekem_public_key * beekem_secret_key
  proc shared_key(
    public_key : beekem_public_key,
    secret_key : beekem_secret_key
  ) : beekem_symmetric_key
}.

module type BEEKEM_NIKE_KEY_SAMPLER = {
  proc sample() : beekem_symmetric_key
}.

type beekem_nike_registration = {
  bnr_handle : int;
  bnr_public_key : beekem_public_key;
  bnr_secret_key : beekem_secret_key
}.

op beekem_nike_registration_for
    (registrations : beekem_nike_registration list)
    (handle : int) : beekem_nike_registration option =
  with registrations = [] => None
  with registrations = registration :: rest =>
    if registration.`bnr_handle = handle
    then Some registration
    else beekem_nike_registration_for rest handle.

type beekem_hkr_cks_query = [
  | BeeNikeRegisterQuery of int & beekem_public_key
  | BeeNikeTestQuery of int & int & bool
].

module type BEEKEM_HKR_CKS_ORACLES = {
  proc register() : int * beekem_public_key
  proc test(
    left_handle : int,
    right_handle : int
  ) : beekem_symmetric_key option
}.

module type BEEKEM_HKR_CKS_ADVERSARY(O : BEEKEM_HKR_CKS_ORACLES) = {
  proc distinguish() : bool
}.

module BeeKemHkrCksOracles(
  N : BEEKEM_NIKE,
  R : BEEKEM_NIKE_KEY_SAMPLER
) = {
  var hidden_bit : bool
  var registrations : beekem_nike_registration list
  var query_log : beekem_hkr_cks_query list
  var registration_count : int
  var test_count : int
  var real_test_count : int
  var random_test_count : int

  proc initialize(bit : bool) : unit = {
    hidden_bit <- bit;
    registrations <- [];
    query_log <- [];
    registration_count <- 0;
    test_count <- 0;
    real_test_count <- 0;
    random_test_count <- 0;
  }

  proc register() : int * beekem_public_key = {
    var public_key : beekem_public_key;
    var secret_key : beekem_secret_key;
    var handle : int;

    (public_key, secret_key) <@ N.keygen();
    handle <- registration_count + 1;
    registration_count <- handle;
    registrations <- rcons registrations
      {| bnr_handle = handle;
         bnr_public_key = public_key;
         bnr_secret_key = secret_key |};
    query_log <- rcons query_log
      (BeeNikeRegisterQuery handle public_key);
    return (handle, public_key);
  }

  proc test(
    left_handle : int,
    right_handle : int
  ) : beekem_symmetric_key option = {
    var left : beekem_nike_registration option;
    var right : beekem_nike_registration option;
    var answer : beekem_symmetric_key;
    var accepted : bool;

    left <- beekem_nike_registration_for registrations left_handle;
    right <- beekem_nike_registration_for registrations right_handle;
    answer <- witness;
    accepted <-
         left <> None
      /\ right <> None
      /\ left_handle <> right_handle;

    if (accepted) {
      test_count <- test_count + 1;
      if (hidden_bit) {
        answer <@ N.shared_key(
          (oget right).`bnr_public_key,
          (oget left).`bnr_secret_key
        );
        real_test_count <- real_test_count + 1;
      } else {
        answer <@ R.sample();
        random_test_count <- random_test_count + 1;
      }
    }

    query_log <- rcons query_log
      (BeeNikeTestQuery left_handle right_handle accepted);
    return if accepted then Some answer else None;
  }
}.

type beekem_hkr_cks_evidence = {
  bhc_hidden_bit : bool;
  bhc_adversary_guess : bool;
  bhc_registration_count : int;
  bhc_test_count : int;
  bhc_real_test_count : int;
  bhc_random_test_count : int;
  bhc_query_log : beekem_hkr_cks_query list;
  bhc_win : bool
}.

module BeeKemHkrCksGame(
  A : BEEKEM_HKR_CKS_ADVERSARY,
  N : BEEKEM_NIKE,
  R : BEEKEM_NIKE_KEY_SAMPLER
) = {
  module O = BeeKemHkrCksOracles(N, R)
  module A = A(O)

  var last_evidence : beekem_hkr_cks_evidence

  (* Deterministic branch runner for checker-proved primitive-game controls.
     [main_with_evidence] still samples the hidden bit and delegates to this
     exact path. *)
  proc main_with_fixed_bit(hidden_bit : bool) : beekem_hkr_cks_evidence = {
    var guess : bool;

    O.initialize(hidden_bit);
    guess <@ A.distinguish();
    last_evidence <-
      {| bhc_hidden_bit = hidden_bit;
         bhc_adversary_guess = guess;
         bhc_registration_count = O.registration_count;
         bhc_test_count = O.test_count;
         bhc_real_test_count = O.real_test_count;
         bhc_random_test_count = O.random_test_count;
         bhc_query_log = O.query_log;
         bhc_win = (guess = hidden_bit) |};
    return last_evidence;
  }

  proc main_with_evidence() : beekem_hkr_cks_evidence = {
    var hidden_bit : bool;
    var evidence : beekem_hkr_cks_evidence;

    hidden_bit <$ dbool;
    evidence <@ main_with_fixed_bit(hidden_bit);
    return evidence;
  }

  proc main() : bool = {
    var evidence : beekem_hkr_cks_evidence;
    evidence <@ main_with_evidence();
    return evidence.`bhc_win;
  }
}.

op beekem_hkr_cks_advantage (success_probability : real) : real =
  beekem_normalized_ki_advantage success_probability.

(* -------------------------------------------------------------------- *)
(* Symmetric-encryption multi-user CPA.  All plaintexts have the concrete
   BeeKEM personal-secret carrier type, so the same-length side condition is
   enforced by the type rather than supplied as an adversarial Boolean.  One
   hidden bit is shared across every adaptive challenge query. *)

module type BEEKEM_SYMMETRIC_ENCRYPTION = {
  proc keygen() : beekem_symmetric_key
  proc encrypt(
    key : beekem_symmetric_key,
    message : beekem_secret_key
  ) : beekem_ciphertext
  proc decrypt(
    key : beekem_symmetric_key,
    ciphertext : beekem_ciphertext
  ) : beekem_secret_key option
}.

type beekem_se_registration = {
  bsr_handle : int;
  bsr_key : beekem_symmetric_key
}.

op beekem_se_registration_for
    (registrations : beekem_se_registration list)
    (handle : int) : beekem_se_registration option =
  with registrations = [] => None
  with registrations = registration :: rest =>
    if registration.`bsr_handle = handle
    then Some registration
    else beekem_se_registration_for rest handle.

type beekem_mu_cpa_query = [
  | BeeSeRegisterQuery of int
  | BeeSeEncryptQuery of int & bool
  | BeeSeChallengeQuery of int & bool
].

module type BEEKEM_MU_CPA_ORACLES = {
  proc register_user() : int
  proc encrypt(
    handle : int,
    message : beekem_secret_key
  ) : beekem_ciphertext option
  proc challenge(
    handle : int,
    left_message : beekem_secret_key,
    right_message : beekem_secret_key
  ) : beekem_ciphertext option
}.

module type BEEKEM_MU_CPA_ADVERSARY(O : BEEKEM_MU_CPA_ORACLES) = {
  proc distinguish() : bool
}.

module BeeKemMuCpaOracles(S : BEEKEM_SYMMETRIC_ENCRYPTION) = {
  var hidden_bit : bool
  var registrations : beekem_se_registration list
  var query_log : beekem_mu_cpa_query list
  var user_count : int
  var encryption_count : int
  var challenge_count : int
  var left_challenge_count : int
  var right_challenge_count : int

  proc initialize(bit : bool) : unit = {
    hidden_bit <- bit;
    registrations <- [];
    query_log <- [];
    user_count <- 0;
    encryption_count <- 0;
    challenge_count <- 0;
    left_challenge_count <- 0;
    right_challenge_count <- 0;
  }

  proc register_user() : int = {
    var key : beekem_symmetric_key;
    var handle : int;

    key <@ S.keygen();
    handle <- user_count + 1;
    user_count <- handle;
    registrations <- rcons registrations
      {| bsr_handle = handle; bsr_key = key |};
    query_log <- rcons query_log (BeeSeRegisterQuery handle);
    return handle;
  }

  proc encrypt(
    handle : int,
    message : beekem_secret_key
  ) : beekem_ciphertext option = {
    var registration : beekem_se_registration option;
    var ciphertext : beekem_ciphertext;
    var accepted : bool;

    registration <- beekem_se_registration_for registrations handle;
    ciphertext <- witness;
    accepted <- registration <> None;
    if (accepted) {
      ciphertext <@ S.encrypt((oget registration).`bsr_key, message);
      encryption_count <- encryption_count + 1;
    }
    query_log <- rcons query_log
      (BeeSeEncryptQuery handle accepted);
    return if accepted then Some ciphertext else None;
  }

  proc challenge(
    handle : int,
    left_message : beekem_secret_key,
    right_message : beekem_secret_key
  ) : beekem_ciphertext option = {
    var registration : beekem_se_registration option;
    var selected_message : beekem_secret_key;
    var ciphertext : beekem_ciphertext;
    var accepted : bool;

    registration <- beekem_se_registration_for registrations handle;
    selected_message <- if hidden_bit then left_message else right_message;
    ciphertext <- witness;
    accepted <- registration <> None;
    if (accepted) {
      ciphertext <@ S.encrypt(
        (oget registration).`bsr_key,
        selected_message
      );
      challenge_count <- challenge_count + 1;
      if (hidden_bit) {
        left_challenge_count <- left_challenge_count + 1;
      } else {
        right_challenge_count <- right_challenge_count + 1;
      }
    }
    query_log <- rcons query_log
      (BeeSeChallengeQuery handle accepted);
    return if accepted then Some ciphertext else None;
  }
}.

type beekem_mu_cpa_evidence = {
  bmc_hidden_bit : bool;
  bmc_adversary_guess : bool;
  bmc_user_count : int;
  bmc_encryption_count : int;
  bmc_challenge_count : int;
  bmc_left_challenge_count : int;
  bmc_right_challenge_count : int;
  bmc_query_log : beekem_mu_cpa_query list;
  bmc_win : bool
}.

module BeeKemMuCpaGame(
  A : BEEKEM_MU_CPA_ADVERSARY,
  S : BEEKEM_SYMMETRIC_ENCRYPTION
) = {
  module O = BeeKemMuCpaOracles(S)
  module A = A(O)

  var last_evidence : beekem_mu_cpa_evidence

  (* Deterministic branch runner for checker-proved primitive-game controls.
     [main_with_evidence] still samples the hidden bit and delegates to this
     exact path. *)
  proc main_with_fixed_bit(hidden_bit : bool) : beekem_mu_cpa_evidence = {
    var guess : bool;

    O.initialize(hidden_bit);
    guess <@ A.distinguish();
    last_evidence <-
      {| bmc_hidden_bit = hidden_bit;
         bmc_adversary_guess = guess;
         bmc_user_count = O.user_count;
         bmc_encryption_count = O.encryption_count;
         bmc_challenge_count = O.challenge_count;
         bmc_left_challenge_count = O.left_challenge_count;
         bmc_right_challenge_count = O.right_challenge_count;
         bmc_query_log = O.query_log;
         bmc_win = (guess = hidden_bit) |};
    return last_evidence;
  }

  proc main_with_evidence() : beekem_mu_cpa_evidence = {
    var hidden_bit : bool;
    var evidence : beekem_mu_cpa_evidence;

    hidden_bit <$ dbool;
    evidence <@ main_with_fixed_bit(hidden_bit);
    return evidence;
  }

  proc main() : bool = {
    var evidence : beekem_mu_cpa_evidence;
    evidence <@ main_with_evidence();
    return evidence.`bmc_win;
  }
}.

op beekem_mu_cpa_advantage (success_probability : real) : real =
  beekem_normalized_ki_advantage success_probability.
