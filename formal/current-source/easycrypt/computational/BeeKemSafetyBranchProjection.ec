require import AllCore List FSet DBool.
require import BeeKemTypes BeeKemProtocol BeeKemKiGame.

(* The imported theorem states safety for the sampled hidden-bit experiment.
   This file derives the corresponding fixed-bit safety masses from the same
   executable game, rather than adding separate branch assumptions. *)
section BeeKemSafetyBranchProjection.
  declare module A <: BEEKEM_KI_ADVERSARY.
  declare module P <: BEEKEM_PROTOCOL_ALGORITHMS.

  module G = BeeKemKiGame(A, P).

  module FairBitSafeRunner = {
    var sampled_bit : bool

    proc main(
      users : beekem_user list,
      group : beekem_group,
      kappa : int,
      membership : beekem_dgm
    ) : bool = {
      var evidence : beekem_ki_evidence;

      sampled_bit <$ dbool;
      if (sampled_bit) {
        evidence <@ G.main_with_fixed_bit(
          users, group, kappa, membership, true
        );
      } else {
        evidence <@ G.main_with_fixed_bit(
          users, group, kappa, membership, false
        );
      }
      return evidence.`bke_safe;
    }
  }.

  lemma beekem_sampled_safe_equiv_fair_bit_runner
      &m
      (users : beekem_user list)
      (group : beekem_group)
      (kappa : int)
      (membership : beekem_dgm) :
    Pr[
      G.main_with_evidence(users, group, kappa, membership) @ &m :
        res.`bke_safe
    ] =
    Pr[
      FairBitSafeRunner.main(users, group, kappa, membership) @ &m : res
    ].
  proof.
    byequiv
      (_ : ={users, group, kappa, membership, glob A, glob P}
           ==> res{1}.`bke_safe = res{2}) => //.
    proc.
    rnd.
    if{2}; call (_ : true); auto.
  qed.

  lemma beekem_sampled_safe_probability_is_fixed_bit_average
      &m
      (users : beekem_user list)
      (group : beekem_group)
      (kappa : int)
      (membership : beekem_dgm) :
    Pr[
      G.main_with_evidence(users, group, kappa, membership) @ &m :
        res.`bke_safe
    ] =
      (Pr[
         G.main_with_fixed_bit(
           users, group, kappa, membership, true
         ) @ &m : res.`bke_safe
       ] +
       Pr[
         G.main_with_fixed_bit(
           users, group, kappa, membership, false
         ) @ &m : res.`bke_safe
       ]) / 2%r.
  proof.
    rewrite beekem_sampled_safe_equiv_fair_bit_runner.
    have -> :
      Pr[
        FairBitSafeRunner.main(users, group, kappa, membership) @ &m : res
      ] =
      Pr[
        FairBitSafeRunner.main(users, group, kappa, membership) @ &m :
          res /\ FairBitSafeRunner.sampled_bit
      ] +
      Pr[
        FairBitSafeRunner.main(users, group, kappa, membership) @ &m :
          res /\ ! FairBitSafeRunner.sampled_bit
      ].
    + by rewrite Pr[mu_split FairBitSafeRunner.sampled_bit].

    have Htrue :
      Pr[
        FairBitSafeRunner.main(users, group, kappa, membership) @ &m :
          res /\ FairBitSafeRunner.sampled_bit
      ] =
      1%r / 2%r *
      Pr[
        G.main_with_fixed_bit(
          users, group, kappa, membership, true
        ) @ &m : res.`bke_safe
      ].
    + byphoare (_ :
          (glob G) = (glob G){m} /\
          arg = (users, group, kappa, membership)
       ==>
          res /\ FairBitSafeRunner.sampled_bit) => //.
      proc.
      pose p := Pr[
        G.main_with_fixed_bit(
          users, group, kappa, membership, true
        ) @ &m : res.`bke_safe
      ].
      seq 1 :
        (FairBitSafeRunner.sampled_bit = true /\
         arg = (users, group, kappa, membership))
        (1%r / 2%r) p _ 0%r
        ((glob G) = (glob G){m} /\
         arg = (users, group, kappa, membership));
        first by auto.
      + by rnd (pred1 true); skip => />; rewrite dbool1E.
      + if; last by (conseq (_ : false ==> _); 1:by smt()); auto.
        conseq (_ : _ ==> evidence.`bke_safe) => //; first by smt().
        call (_ :
          arg = (users, group, kappa, membership, true) /\
          (glob G) = (glob G){m}
          ==> res.`bke_safe); last by auto.
        by bypr => &m0 hm0; rewrite /p; byequiv => //; proc (true).
      + by (conseq (_ : _ ==> false); 1:smt()); auto.
      smt().

    have Hfalse :
      Pr[
        FairBitSafeRunner.main(users, group, kappa, membership) @ &m :
          res /\ ! FairBitSafeRunner.sampled_bit
      ] =
      1%r / 2%r *
      Pr[
        G.main_with_fixed_bit(
          users, group, kappa, membership, false
        ) @ &m : res.`bke_safe
      ].
    + byphoare (_ :
          (glob G) = (glob G){m} /\
          arg = (users, group, kappa, membership)
       ==>
          res /\ ! FairBitSafeRunner.sampled_bit) => //.
      proc.
      pose p := Pr[
        G.main_with_fixed_bit(
          users, group, kappa, membership, false
        ) @ &m : res.`bke_safe
      ].
      seq 1 :
        (FairBitSafeRunner.sampled_bit = false /\
         arg = (users, group, kappa, membership))
        (1%r / 2%r) p _ 0%r
        ((glob G) = (glob G){m} /\
         arg = (users, group, kappa, membership));
        first by auto.
      + by rnd (pred1 false); skip => />; rewrite dbool1E.
      + if; first by (conseq (_ : false ==> _); 1:by smt()); auto.
        conseq (_ : _ ==> evidence.`bke_safe) => //; first by smt().
        call (_ :
          arg = (users, group, kappa, membership, false) /\
          (glob G) = (glob G){m}
          ==> res.`bke_safe); last by auto.
        by bypr => &m0 hm0; rewrite /p; byequiv => //; proc (true).
      + by (conseq (_ : _ ==> false); 1:smt()); auto.
      smt().

    rewrite Htrue Hfalse.
    smt().
  qed.

  lemma beekem_sampled_safe_one_implies_fixed_safe_one
      &m
      (users : beekem_user list)
      (group : beekem_group)
      (kappa : int)
      (membership : beekem_dgm) :
    Pr[
      G.main_with_evidence(users, group, kappa, membership) @ &m :
        res.`bke_safe
    ] = 1%r =>
    Pr[
      G.main_with_fixed_bit(
        users, group, kappa, membership, true
      ) @ &m : res.`bke_safe
    ] = 1%r /\
    Pr[
      G.main_with_fixed_bit(
        users, group, kappa, membership, false
      ) @ &m : res.`bke_safe
    ] = 1%r.
  proof.
    move=> Hsampled.
    have Haverage :=
      beekem_sampled_safe_probability_is_fixed_bit_average
        &m users group kappa membership.
    smt(mu_bounded ge0_mu).
  qed.
end section BeeKemSafetyBranchProjection.
