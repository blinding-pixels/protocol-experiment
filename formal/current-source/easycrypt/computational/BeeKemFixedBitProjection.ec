require import AllCore List FSet.
require import BeeKemTypes BeeKemProtocol BeeKemKiGame.
require import BeeKemExecutableNormalization.

(* Probability-level view of the exact evidence characterization.  The two
   events are evaluated on the same executable fixed-bit KI experiment; no
   safety, consistency, or adversary-success premise is introduced here. *)
section BeeKemFixedBitProjection.
  declare module A <: BEEKEM_KI_ADVERSARY.
  declare module P <: BEEKEM_PROTOCOL_ALGORITHMS.

  module G = BeeKemKiGame(A, P).

  lemma beekem_fixed_bit_win_probability_is_semantic
      &m
      (users : beekem_user list)
      (group : beekem_group)
      (kappa : int)
      (membership : beekem_dgm)
      (hidden_bit : bool) :
    Pr[
      G.main_with_fixed_bit(
        users, group, kappa, membership, hidden_bit
      ) @ &m : res.`bke_win
    ] =
    Pr[
      G.main_with_fixed_bit(
        users, group, kappa, membership, hidden_bit
      ) @ &m :
        beekem_ki_final_win
          res.`bke_safe
          res.`bke_protocol_consistency_failure
          res.`bke_adversary_guess
          res.`bke_hidden_bit
    ].
  proof.
    byequiv
      (_ : ={users, group, kappa, membership, hidden_bit,
             glob A, glob P}
           ==>
           res{1}.`bke_win =
             beekem_ki_final_win
               res{2}.`bke_safe
               res{2}.`bke_protocol_consistency_failure
               res{2}.`bke_adversary_guess
               res{2}.`bke_hidden_bit) => //.
    proc.
    call (_ : true).
    call (_ : true).
    auto.
  qed.
end section BeeKemFixedBitProjection.
