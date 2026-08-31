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
    byequiv
      (_ : ={users, group, kappa, membership, glob A, glob P}
           ==>
           beekem_ki_final_win
             res{1}.`bke_safe
             res{1}.`bke_protocol_consistency_failure
             res{1}.`bke_adversary_guess
             res{1}.`bke_hidden_bit =
           (res{2}.`bke_safe /\
            (res{2}.`bke_protocol_consistency_failure \/
             res{2}.`bke_adversary_guess))) => //.
    proc.
    call (_ : true).
    call (_ : true).
    auto.
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
    + smt(mu_bounded ge0_mu).

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
    byequiv
      (_ : ={users, group, kappa, membership, glob A, glob P}
           ==>
           beekem_ki_final_win
             res{1}.`bke_safe
             res{1}.`bke_protocol_consistency_failure
             res{1}.`bke_adversary_guess
             res{1}.`bke_hidden_bit =
           (res{2}.`bke_safe /\
            (res{2}.`bke_protocol_consistency_failure \/
             ! res{2}.`bke_adversary_guess))) => //.
    proc.
    call (_ : true).
    call (_ : true).
    auto.
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
