require import AllCore List FSet.
require import BeeKemTypes BeeKemPrimitiveGames BeeKemPrimitiveContracts.

(* Deliberately correct but insecure primitive implementations.  These are
   negative controls only: their actual named primitive games are winnable with
   probability one, demonstrating that neither primitive advantage is a
   decorative operator. *)
op beekem_insecure_nike_public : beekem_public_key = BeeKemPublicKey 801.
op beekem_insecure_nike_secret : beekem_secret_key = BeeKemSecretKey 802.
op beekem_insecure_nike_real_key : beekem_symmetric_key = BeeKemSymmetricKey 803.
op beekem_insecure_nike_random_key : beekem_symmetric_key = BeeKemSymmetricKey 804.

module BeeKemInsecureNike : BEEKEM_NIKE = {
  proc keygen() : beekem_public_key * beekem_secret_key = {
    return (beekem_insecure_nike_public, beekem_insecure_nike_secret);
  }

  proc shared_key(
    public_key : beekem_public_key,
    secret_key : beekem_secret_key
  ) : beekem_symmetric_key = {
    return beekem_insecure_nike_real_key;
  }
}.

module BeeKemInsecureNikeRandom : BEEKEM_NIKE_KEY_SAMPLER = {
  proc sample() : beekem_symmetric_key = {
    return beekem_insecure_nike_random_key;
  }
}.

module BeeKemInsecureNikeAdversary(O : BEEKEM_HKR_CKS_ORACLES) = {
  proc distinguish() : bool = {
    var left : int * beekem_public_key;
    var right : int * beekem_public_key;
    var answer : beekem_symmetric_key option;

    left <@ O.register();
    right <@ O.register();
    answer <@ O.test(left.`1, right.`1);
    return answer = Some beekem_insecure_nike_real_key;
  }
}.

module BeeKemInsecureNikeGame =
  BeeKemHkrCksGame(
    BeeKemInsecureNikeAdversary,
    BeeKemInsecureNike,
    BeeKemInsecureNikeRandom
  ).

lemma beekem_insecure_nike_real_branch_wins :
  hoare [BeeKemInsecureNikeGame.main_with_fixed_bit :
    hidden_bit = true ==>
       res.`bhc_hidden_bit
    /\ res.`bhc_adversary_guess
    /\ res.`bhc_registration_count = 2
    /\ res.`bhc_test_count = 1
    /\ res.`bhc_real_test_count = 1
    /\ res.`bhc_random_test_count = 0
    /\ res.`bhc_win].
proof.
  proc.
  inline *.
  auto.
  rewrite /beekem_nike_registration_for.
  smt().
qed.

lemma beekem_insecure_nike_random_branch_wins :
  hoare [BeeKemInsecureNikeGame.main_with_fixed_bit :
    hidden_bit = false ==>
       ! res.`bhc_hidden_bit
    /\ ! res.`bhc_adversary_guess
    /\ res.`bhc_registration_count = 2
    /\ res.`bhc_test_count = 1
    /\ res.`bhc_real_test_count = 0
    /\ res.`bhc_random_test_count = 1
    /\ res.`bhc_win].
proof.
  proc.
  inline *.
  auto.
  rewrite /beekem_nike_registration_for
    /beekem_insecure_nike_real_key /beekem_insecure_nike_random_key.
  smt().
qed.

lemma beekem_insecure_nike_game_probability_one &m :
  Pr[BeeKemInsecureNikeGame.main() @ &m : res] = 1%r.
proof.
  byphoare => //.
  proc.
  inline BeeKemInsecureNikeGame.main_with_evidence.
  seq 1 : true 1%r.
  + rnd.
  call (: true ==> res.`bhc_win).
  + case (hidden_bit).
    + conseq beekem_insecure_nike_real_branch_wins => //.
    + conseq beekem_insecure_nike_random_branch_wins => //.
  auto.
qed.

lemma beekem_insecure_nike_is_symmetric &m :
  Pr[BeeKemNikeSymmetryGame(BeeKemInsecureNike).main() @ &m : res] = 1%r.
proof.
  byphoare => //.
  proc.
  inline *.
  auto.
qed.

op beekem_insecure_se_key : beekem_symmetric_key = BeeKemSymmetricKey 811.
op beekem_insecure_se_left : beekem_secret_key = BeeKemSecretKey 812.
op beekem_insecure_se_right : beekem_secret_key = BeeKemSecretKey 813.

op beekem_insecure_ciphertext_of
    (message : beekem_secret_key) : beekem_ciphertext =
  with message = BeeKemSecretKey value => BeeKemCiphertext value.

op beekem_insecure_plaintext_of
    (ciphertext : beekem_ciphertext) : beekem_secret_key =
  with ciphertext = BeeKemCiphertext value => BeeKemSecretKey value.

module BeeKemInsecureSe : BEEKEM_SYMMETRIC_ENCRYPTION = {
  proc keygen() : beekem_symmetric_key = {
    return beekem_insecure_se_key;
  }

  proc encrypt(
    key : beekem_symmetric_key,
    message : beekem_secret_key
  ) : beekem_ciphertext = {
    return beekem_insecure_ciphertext_of message;
  }

  proc decrypt(
    key : beekem_symmetric_key,
    ciphertext : beekem_ciphertext
  ) : beekem_secret_key option = {
    return Some (beekem_insecure_plaintext_of ciphertext);
  }
}.

module BeeKemInsecureSeAdversary(O : BEEKEM_MU_CPA_ORACLES) = {
  proc distinguish() : bool = {
    var handle : int;
    var answer : beekem_ciphertext option;

    handle <@ O.register_user();
    answer <@ O.challenge(
      handle,
      beekem_insecure_se_left,
      beekem_insecure_se_right
    );
    return answer = Some (beekem_insecure_ciphertext_of beekem_insecure_se_left);
  }
}.

module BeeKemInsecureSeGame =
  BeeKemMuCpaGame(BeeKemInsecureSeAdversary, BeeKemInsecureSe).

lemma beekem_insecure_se_left_branch_wins :
  hoare [BeeKemInsecureSeGame.main_with_fixed_bit :
    hidden_bit = true ==>
       res.`bmc_hidden_bit
    /\ res.`bmc_adversary_guess
    /\ res.`bmc_user_count = 1
    /\ res.`bmc_challenge_count = 1
    /\ res.`bmc_left_challenge_count = 1
    /\ res.`bmc_right_challenge_count = 0
    /\ res.`bmc_win].
proof.
  proc.
  inline *.
  auto.
  rewrite /beekem_se_registration_for.
  smt().
qed.

lemma beekem_insecure_se_right_branch_wins :
  hoare [BeeKemInsecureSeGame.main_with_fixed_bit :
    hidden_bit = false ==>
       ! res.`bmc_hidden_bit
    /\ ! res.`bmc_adversary_guess
    /\ res.`bmc_user_count = 1
    /\ res.`bmc_challenge_count = 1
    /\ res.`bmc_left_challenge_count = 0
    /\ res.`bmc_right_challenge_count = 1
    /\ res.`bmc_win].
proof.
  proc.
  inline *.
  auto.
  rewrite /beekem_se_registration_for
    /beekem_insecure_ciphertext_of
    /beekem_insecure_se_left /beekem_insecure_se_right.
  smt().
qed.

lemma beekem_insecure_se_game_probability_one &m :
  Pr[BeeKemInsecureSeGame.main() @ &m : res] = 1%r.
proof.
  byphoare => //.
  proc.
  inline BeeKemInsecureSeGame.main_with_evidence.
  seq 1 : true 1%r.
  + rnd.
  call (: true ==> res.`bmc_win).
  + case (hidden_bit).
    + conseq beekem_insecure_se_left_branch_wins => //.
    + conseq beekem_insecure_se_right_branch_wins => //.
  auto.
qed.

lemma beekem_insecure_se_is_correct
    &m (message : beekem_secret_key) :
  Pr[
    BeeKemSeCorrectnessGame(BeeKemInsecureSe).main(message) @ &m : res
  ] = 1%r.
proof.
  byphoare => //.
  proc.
  inline *.
  auto.
  case message => value.
  rewrite /beekem_insecure_ciphertext_of /beekem_insecure_plaintext_of.
  auto.
qed.
