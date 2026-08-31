require import AllCore.
require import BeeKemTypes BeeKemPrimitiveGames.

(* -------------------------------------------------------------------- *)
(* Correctness contracts implicit in the paper's primitive definitions.  They
   are executable games so Theorem 1 can state compatibility side conditions
   without an unconstrained Boolean. *)
module BeeKemNikeSymmetryGame(N : BEEKEM_NIKE) = {
  proc main() : bool = {
    var left_public : beekem_public_key;
    var left_secret : beekem_secret_key;
    var right_public : beekem_public_key;
    var right_secret : beekem_secret_key;
    var left_key : beekem_symmetric_key;
    var right_key : beekem_symmetric_key;

    (left_public, left_secret) <@ N.keygen();
    (right_public, right_secret) <@ N.keygen();
    left_key <@ N.shared_key(right_public, left_secret);
    right_key <@ N.shared_key(left_public, right_secret);
    return left_key = right_key;
  }
}.

module BeeKemSeCorrectnessGame(S : BEEKEM_SYMMETRIC_ENCRYPTION) = {
  proc main(message : beekem_secret_key) : bool = {
    var key : beekem_symmetric_key;
    var ciphertext : beekem_ciphertext;
    var recovered : beekem_secret_key option;

    key <@ S.keygen();
    ciphertext <@ S.encrypt(key, message);
    recovered <@ S.decrypt(key, ciphertext);
    return recovered = Some message;
  }
}.
