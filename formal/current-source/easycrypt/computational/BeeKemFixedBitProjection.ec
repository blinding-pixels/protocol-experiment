require import AllCore List FSet.
require import BeeKemTypes BeeKemProtocol BeeKemKiGame.

(* Probability-level view of the exact evidence characterization.  The two
   events are evaluated on the same executable fixed-bit KI experiment; no
   safety, consistency, or adversary-success premise is introduced here. *)
section BeeKemFixedBitProjection.
  declare module A <: BEEKEM_KI_ADVERSARY.
  declare module P <: BEEKEM_PROTOCOL_ALGORITHMS.

  module G = BeeKemKiGame(A, P).


  (* Both predicates below observe one execution.  Using a same-run event
     partition avoids an unnecessary two-run simulation of opaque adversaries. *)
  lemma beekem_fixed_bit_output_relation (bit : bool) :
    hoare [G.main_with_fixed_bit : hidden_bit = bit ==>
      res.`bke_hidden_bit = bit /\
      res.`bke_win = beekem_ki_final_win res.`bke_safe
        res.`bke_protocol_consistency_failure res.`bke_adversary_guess bit].
  proof.
    proc; wp.
    call (_ : true ==> true); first by conseq (_ : _ ==> true).
    call (_ : true ==> true); first by conseq (_ : _ ==> true).
    by auto.
  qed.

  lemma beekem_fixed_bit_replace_event
      &m (users : beekem_user list) (group : beekem_group)
      (kappa : int) (membership : beekem_dgm) (bit : bool)
      (p q : beekem_ki_evidence -> bool) :
    (forall evidence,
       evidence.`bke_hidden_bit = bit /\
       evidence.`bke_win = beekem_ki_final_win evidence.`bke_safe
         evidence.`bke_protocol_consistency_failure
         evidence.`bke_adversary_guess bit =>
       (p evidence <=> q evidence)) =>
    Pr[G.main_with_fixed_bit(users, group, kappa, membership, bit) @ &m : p res] =
    Pr[G.main_with_fixed_bit(users, group, kappa, membership, bit) @ &m : q res].
  proof.
    move=> Hevent.
    have Hp_only :
      Pr[G.main_with_fixed_bit(users, group, kappa, membership, bit) @ &m :
         p res /\ ! q res] = 0%r.
    + byphoare (_ : hidden_bit = bit ==> p res /\ ! q res) => //.
      hoare.
      conseq (beekem_fixed_bit_output_relation bit) => //.
      smt().
    have Hq_only :
      Pr[G.main_with_fixed_bit(users, group, kappa, membership, bit) @ &m :
         q res /\ ! p res] = 0%r.
    + byphoare (_ : hidden_bit = bit ==> q res /\ ! p res) => //.
      hoare.
      conseq (beekem_fixed_bit_output_relation bit) => //.
      smt().
    have Hp :
      Pr[G.main_with_fixed_bit(users, group, kappa, membership, bit) @ &m : p res] =
      Pr[G.main_with_fixed_bit(users, group, kappa, membership, bit) @ &m : p res /\ q res] +
      Pr[G.main_with_fixed_bit(users, group, kappa, membership, bit) @ &m : p res /\ ! q res].
    + by rewrite Pr[mu_split (q res)].
    have Hq :
      Pr[G.main_with_fixed_bit(users, group, kappa, membership, bit) @ &m : q res] =
      Pr[G.main_with_fixed_bit(users, group, kappa, membership, bit) @ &m : q res /\ p res] +
      Pr[G.main_with_fixed_bit(users, group, kappa, membership, bit) @ &m : q res /\ ! p res].
    + by rewrite Pr[mu_split (p res)].
    have Hboth :
      Pr[G.main_with_fixed_bit(users, group, kappa, membership, bit) @ &m : p res /\ q res] =
      Pr[G.main_with_fixed_bit(users, group, kappa, membership, bit) @ &m : q res /\ p res].
    + by rewrite Pr[mu_eq] /#.
    smt().
  qed.

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
    apply (beekem_fixed_bit_replace_event &m users group kappa membership hidden_bit
      (fun e => e.`bke_win) (fun e => beekem_ki_final_win e.`bke_safe e.`bke_protocol_consistency_failure e.`bke_adversary_guess e.`bke_hidden_bit)).
    by move=> evidence [Hbit Hwin]; rewrite /= Hbit Hwin.
  qed.

  lemma beekem_fixed_true_semantic_probability_is_boolean_event
      &m
      (users : beekem_user list)
      (group : beekem_group)
      (kappa : int)
      (membership : beekem_dgm) :
    Pr[
      G.main_with_fixed_bit(
        users, group, kappa, membership, true
      ) @ &m :
        beekem_ki_final_win
          res.`bke_safe
          res.`bke_protocol_consistency_failure
          res.`bke_adversary_guess
          res.`bke_hidden_bit
    ] =
    Pr[
      G.main_with_fixed_bit(
        users, group, kappa, membership, true
      ) @ &m :
        res.`bke_safe /\
        (res.`bke_protocol_consistency_failure \/
         res.`bke_adversary_guess)
    ].
  proof.
    apply (beekem_fixed_bit_replace_event &m users group kappa membership true
      (fun e => beekem_ki_final_win e.`bke_safe e.`bke_protocol_consistency_failure e.`bke_adversary_guess e.`bke_hidden_bit) (fun e => e.`bke_safe /\ (e.`bke_protocol_consistency_failure \/ e.`bke_adversary_guess))).
    move=> evidence [Hbit Hwin]; rewrite /= Hbit /beekem_ki_final_win /=.
    smt().
  qed.

  (* On the real branch, exact probability-one mass for a safe,
     protocol-consistent execution removes only the protocol-failure auto-win.
     The remaining KI win event is precisely the application projection. *)
  lemma beekem_fixed_true_win_probability_is_projected
      &m
      (users : beekem_user list)
      (group : beekem_group)
      (kappa : int)
      (membership : beekem_dgm) :
    Pr[
      G.main_with_fixed_bit(
        users, group, kappa, membership, true
      ) @ &m :
        res.`bke_safe /\
        ! res.`bke_protocol_consistency_failure
    ] = 1%r =>
    Pr[
      G.main_with_fixed_bit(
        users, group, kappa, membership, true
      ) @ &m : res.`bke_win
    ] =
    Pr[
      G.main_with_fixed_bit(
        users, group, kappa, membership, true
      ) @ &m :
        res.`bke_safe /\
        ! res.`bke_protocol_consistency_failure /\
        res.`bke_adversary_guess
    ].
  proof.
    move=> Hgood.
    rewrite
      (beekem_fixed_bit_win_probability_is_semantic
         &m users group kappa membership true)
      (beekem_fixed_true_semantic_probability_is_boolean_event
         &m users group kappa membership).

    have Hsafe_partition :
      Pr[
        G.main_with_fixed_bit(
          users, group, kappa, membership, true
        ) @ &m : res.`bke_safe
      ] =
      Pr[
        G.main_with_fixed_bit(
          users, group, kappa, membership, true
        ) @ &m :
          res.`bke_safe /\
          ! res.`bke_protocol_consistency_failure
      ] +
      Pr[
        G.main_with_fixed_bit(
          users, group, kappa, membership, true
        ) @ &m :
          res.`bke_safe /\
          res.`bke_protocol_consistency_failure
      ].
    + have -> :
        Pr[
          G.main_with_fixed_bit(
            users, group, kappa, membership, true
          ) @ &m : res.`bke_safe
        ] =
        Pr[
          G.main_with_fixed_bit(
            users, group, kappa, membership, true
          ) @ &m :
            (res.`bke_safe /\
             ! res.`bke_protocol_consistency_failure) \/
            (res.`bke_safe /\
             res.`bke_protocol_consistency_failure)
        ].
      + by rewrite Pr[mu_eq] /#.
      by rewrite Pr[mu_disjoint] 1:/#.

    have Hfailure_zero :
      Pr[
        G.main_with_fixed_bit(
          users, group, kappa, membership, true
        ) @ &m :
          res.`bke_safe /\
          res.`bke_protocol_consistency_failure
      ] = 0%r.
    + smt(Distr.mu_bounded Distr.ge0_mu).

    have Hsemantic_partition :
      Pr[
        G.main_with_fixed_bit(
          users, group, kappa, membership, true
        ) @ &m :
          res.`bke_safe /\
          (res.`bke_protocol_consistency_failure \/
           res.`bke_adversary_guess)
      ] =
      Pr[
        G.main_with_fixed_bit(
          users, group, kappa, membership, true
        ) @ &m :
          res.`bke_safe /\
          ! res.`bke_protocol_consistency_failure /\
          res.`bke_adversary_guess
      ] +
      Pr[
        G.main_with_fixed_bit(
          users, group, kappa, membership, true
        ) @ &m :
          res.`bke_safe /\
          res.`bke_protocol_consistency_failure
      ].
    + have -> :
        Pr[
          G.main_with_fixed_bit(
            users, group, kappa, membership, true
          ) @ &m :
            res.`bke_safe /\
            (res.`bke_protocol_consistency_failure \/
             res.`bke_adversary_guess)
        ] =
        Pr[
          G.main_with_fixed_bit(
            users, group, kappa, membership, true
          ) @ &m :
            (res.`bke_safe /\
             ! res.`bke_protocol_consistency_failure /\
             res.`bke_adversary_guess) \/
            (res.`bke_safe /\
             res.`bke_protocol_consistency_failure)
        ].
      + by rewrite Pr[mu_eq] /#.
      by rewrite Pr[mu_disjoint] 1:/#.

    smt().
  qed.

  lemma beekem_fixed_false_semantic_probability_is_boolean_event
      &m
      (users : beekem_user list)
      (group : beekem_group)
      (kappa : int)
      (membership : beekem_dgm) :
    Pr[
      G.main_with_fixed_bit(
        users, group, kappa, membership, false
      ) @ &m :
        beekem_ki_final_win
          res.`bke_safe
          res.`bke_protocol_consistency_failure
          res.`bke_adversary_guess
          res.`bke_hidden_bit
    ] =
    Pr[
      G.main_with_fixed_bit(
        users, group, kappa, membership, false
      ) @ &m :
        res.`bke_safe /\
        (res.`bke_protocol_consistency_failure \/
         ! res.`bke_adversary_guess)
    ].
  proof.
    apply (beekem_fixed_bit_replace_event &m users group kappa membership false
      (fun e => beekem_ki_final_win e.`bke_safe e.`bke_protocol_consistency_failure e.`bke_adversary_guess e.`bke_hidden_bit) (fun e => e.`bke_safe /\ (e.`bke_protocol_consistency_failure \/ ! e.`bke_adversary_guess))).
    move=> evidence [Hbit Hwin]; rewrite /= Hbit /beekem_ki_final_win /=.
    smt().
  qed.

  (* On the random-root branch, the KI win event and the projected one-event
     form an exact partition of the challenger-computed safe mass. *)
  lemma beekem_fixed_false_win_probability_is_projected_complement
      &m
      (users : beekem_user list)
      (group : beekem_group)
      (kappa : int)
      (membership : beekem_dgm) :
    Pr[
      G.main_with_fixed_bit(
        users, group, kappa, membership, false
      ) @ &m : res.`bke_safe
    ] = 1%r =>
    Pr[
      G.main_with_fixed_bit(
        users, group, kappa, membership, false
      ) @ &m : res.`bke_win
    ] =
    1%r -
    Pr[
      G.main_with_fixed_bit(
        users, group, kappa, membership, false
      ) @ &m :
        res.`bke_safe /\
        ! res.`bke_protocol_consistency_failure /\
        res.`bke_adversary_guess
    ].
  proof.
    move=> Hsafe.
    rewrite
      (beekem_fixed_bit_win_probability_is_semantic
         &m users group kappa membership false)
      (beekem_fixed_false_semantic_probability_is_boolean_event
         &m users group kappa membership).

    have Hsafe_partition :
      Pr[
        G.main_with_fixed_bit(
          users, group, kappa, membership, false
        ) @ &m : res.`bke_safe
      ] =
      Pr[
        G.main_with_fixed_bit(
          users, group, kappa, membership, false
        ) @ &m :
          res.`bke_safe /\
          (res.`bke_protocol_consistency_failure \/
           ! res.`bke_adversary_guess)
      ] +
      Pr[
        G.main_with_fixed_bit(
          users, group, kappa, membership, false
        ) @ &m :
          res.`bke_safe /\
          ! res.`bke_protocol_consistency_failure /\
          res.`bke_adversary_guess
      ].
    + have -> :
        Pr[
          G.main_with_fixed_bit(
            users, group, kappa, membership, false
          ) @ &m : res.`bke_safe
        ] =
        Pr[
          G.main_with_fixed_bit(
            users, group, kappa, membership, false
          ) @ &m :
            (res.`bke_safe /\
             (res.`bke_protocol_consistency_failure \/
              ! res.`bke_adversary_guess)) \/
            (res.`bke_safe /\
             ! res.`bke_protocol_consistency_failure /\
             res.`bke_adversary_guess)
        ].
      + by rewrite Pr[mu_eq] /#.
      by rewrite Pr[mu_disjoint] 1:/#.

    smt().
  qed.
end section BeeKemFixedBitProjection.
