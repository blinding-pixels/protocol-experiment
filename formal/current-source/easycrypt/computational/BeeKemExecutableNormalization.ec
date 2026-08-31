require import AllCore List FSet DBool.
require import BeeKemTypes BeeKemProtocol BeeKemKiGame.

(* Kernel connection between the executable fair-bit KI-DCGKA game and its two
   fixed-bit executions.  The theorem is generic in the BeeKEM adversary and
   protocol implementation, so the authoritative application reduction can
   instantiate it without assuming an adjacent hybrid hop. *)
section ExecutableBeeKemNormalization.
  declare module A <: BEEKEM_KI_ADVERSARY.
  declare module P <: BEEKEM_PROTOCOL_ALGORITHMS.

  module G = BeeKemKiGame(A, P).

  module FairBitRunner = {
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
      return evidence.`bke_win;
    }
  }.

  lemma beekem_sampled_game_equiv_fair_bit_runner
      &m
      (users : beekem_user list)
      (group : beekem_group)
      (kappa : int)
      (membership : beekem_dgm) :
    Pr[G.main(users, group, kappa, membership) @ &m : res] =
    Pr[FairBitRunner.main(users, group, kappa, membership) @ &m : res].
  proof.
    byequiv => //.
    proc.
    inline G.main_with_evidence.
    rnd.
    if{2}; call (_ : true); auto.
  qed.

  lemma beekem_sampled_win_probability_is_fixed_bit_average
      &m
      (users : beekem_user list)
      (group : beekem_group)
      (kappa : int)
      (membership : beekem_dgm) :
    Pr[G.main(users, group, kappa, membership) @ &m : res] =
      (Pr[
         G.main_with_fixed_bit(
           users, group, kappa, membership, true
         ) @ &m : res.`bke_win
       ] +
       Pr[
         G.main_with_fixed_bit(
           users, group, kappa, membership, false
         ) @ &m : res.`bke_win
       ]) / 2%r.
  proof.
    rewrite beekem_sampled_game_equiv_fair_bit_runner.
    have -> :
      Pr[
        FairBitRunner.main(users, group, kappa, membership) @ &m : res
      ] =
      Pr[
        FairBitRunner.main(users, group, kappa, membership) @ &m :
          res /\ FairBitRunner.sampled_bit
      ] +
      Pr[
        FairBitRunner.main(users, group, kappa, membership) @ &m :
          res /\ ! FairBitRunner.sampled_bit
      ].
    + by rewrite Pr[mu_split FairBitRunner.sampled_bit].

    have Htrue :
      Pr[
        FairBitRunner.main(users, group, kappa, membership) @ &m :
          res /\ FairBitRunner.sampled_bit
      ] =
      1%r / 2%r *
      Pr[
        G.main_with_fixed_bit(
          users, group, kappa, membership, true
        ) @ &m : res.`bke_win
      ].
    + byphoare (_ :
          (glob G) = (glob G){m} /\
          arg = (users, group, kappa, membership)
       ==>
          res /\ FairBitRunner.sampled_bit) => //.
      proc.
      pose p := Pr[
        G.main_with_fixed_bit(
          users, group, kappa, membership, true
        ) @ &m : res.`bke_win
      ].
      seq 1 :
        (FairBitRunner.sampled_bit = true /\
         arg = (users, group, kappa, membership))
        (1%r / 2%r) p _ 0%r
        ((glob G) = (glob G){m} /\
         arg = (users, group, kappa, membership));
        first by auto.
      + by rnd (pred1 true); skip => />; rewrite dbool1E.
      + if; last by (conseq (_ : false ==> _); 1:by smt()); auto.
        conseq (_ : _ ==> evidence.`bke_win) => //; first by smt().
        call (_ :
          arg = (users, group, kappa, membership, true) /\
          (glob G) = (glob G){m}
          ==> res.`bke_win); last by auto.
        by bypr => &m0 hm0; rewrite /p; byequiv => //; proc (true).
      + by (conseq (_ : _ ==> false); 1:smt()); auto.
      smt().

    have Hfalse :
      Pr[
        FairBitRunner.main(users, group, kappa, membership) @ &m :
          res /\ ! FairBitRunner.sampled_bit
      ] =
      1%r / 2%r *
      Pr[
        G.main_with_fixed_bit(
          users, group, kappa, membership, false
        ) @ &m : res.`bke_win
      ].
    + byphoare (_ :
          (glob G) = (glob G){m} /\
          arg = (users, group, kappa, membership)
       ==>
          res /\ ! FairBitRunner.sampled_bit) => //.
      proc.
      pose p := Pr[
        G.main_with_fixed_bit(
          users, group, kappa, membership, false
        ) @ &m : res.`bke_win
      ].
      seq 1 :
        (FairBitRunner.sampled_bit = false /\
         arg = (users, group, kappa, membership))
        (1%r / 2%r) p _ 0%r
        ((glob G) = (glob G){m} /\
         arg = (users, group, kappa, membership));
        first by auto.
      + by rnd (pred1 false); skip => />; rewrite dbool1E.
      + if; first by (conseq (_ : false ==> _); 1:by smt()); auto.
        conseq (_ : _ ==> evidence.`bke_win) => //; first by smt().
        call (_ :
          arg = (users, group, kappa, membership, false) /\
          (glob G) = (glob G){m}
          ==> res.`bke_win); last by auto.
        by bypr => &m0 hm0; rewrite /p; byequiv => //; proc (true).
      + by (conseq (_ : _ ==> false); 1:smt()); auto.
      smt().

    rewrite Htrue Hfalse.
    smt().
  qed.

  (* The fixed-bit runner records the challenger-computed safety event,
     protocol-consistency flag, adversary guess, and final win bit in one
     evidence value.  This theorem exposes their exact relation for later
     probability algebra; it does not assume safety or correctness. *)
  lemma beekem_fixed_bit_evidence_characterization
      (users : beekem_user list)
      (group : beekem_group)
      (kappa : int)
      (membership : beekem_dgm)
      (hidden_bit : bool) :
    hoare[
      G.main_with_fixed_bit :
        arg = (users, group, kappa, membership, hidden_bit)
        ==>
        res.`bke_hidden_bit = hidden_bit /\
        res.`bke_win =
          beekem_ki_final_win
            res.`bke_safe
            res.`bke_protocol_consistency_failure
            res.`bke_adversary_guess
            hidden_bit
    ].
  proof.
    proc.
    call (_ : true).
    call (_ : true).
    auto.
  qed.
end section ExecutableBeeKemNormalization.
