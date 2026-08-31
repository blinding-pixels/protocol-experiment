require import AllCore List FSet.
require import BeeKemTypes BeeKemProtocol BeeKemKiGame.

(* Probability-one safety and probability-one protocol consistency combine on
   the same executable fixed-bit experiment.  Protocol consistency remains an
   explicit implementation-faithfulness boundary; this lemma merely derives
   the conjunction required by the projected application event. *)
section BeeKemConsistencyBranchProjection.
  declare module A <: BEEKEM_KI_ADVERSARY.
  declare module P <: BEEKEM_PROTOCOL_ALGORITHMS.

  module G = BeeKemKiGame(A, P).

  lemma beekem_fixed_safe_and_consistent_probability_one
      &m
      (users : beekem_user list)
      (group : beekem_group)
      (kappa : int)
      (membership : beekem_dgm)
      (hidden_bit : bool) :
    Pr[
      G.main_with_fixed_bit(
        users, group, kappa, membership, hidden_bit
      ) @ &m : res.`bke_safe
    ] = 1%r =>
    Pr[
      G.main_with_fixed_bit(
        users, group, kappa, membership, hidden_bit
      ) @ &m : ! res.`bke_protocol_consistency_failure
    ] = 1%r =>
    Pr[
      G.main_with_fixed_bit(
        users, group, kappa, membership, hidden_bit
      ) @ &m :
        res.`bke_safe /\
        ! res.`bke_protocol_consistency_failure
    ] = 1%r.
  proof.
    move=> Hsafe Hconsistent.

    have Hfailure_partition :
      Pr[
        G.main_with_fixed_bit(
          users, group, kappa, membership, hidden_bit
        ) @ &m : true
      ] =
      Pr[
        G.main_with_fixed_bit(
          users, group, kappa, membership, hidden_bit
        ) @ &m : ! res.`bke_protocol_consistency_failure
      ] +
      Pr[
        G.main_with_fixed_bit(
          users, group, kappa, membership, hidden_bit
        ) @ &m : res.`bke_protocol_consistency_failure
      ].
    + have -> :
        Pr[
          G.main_with_fixed_bit(
            users, group, kappa, membership, hidden_bit
          ) @ &m : true
        ] =
        Pr[
          G.main_with_fixed_bit(
            users, group, kappa, membership, hidden_bit
          ) @ &m :
            ! res.`bke_protocol_consistency_failure \/
            res.`bke_protocol_consistency_failure
        ].
      + by rewrite Pr[mu_eq] /#.
      by rewrite Pr[mu_disjoint] 1:/#.

    have Hfailure_zero :
      Pr[
        G.main_with_fixed_bit(
          users, group, kappa, membership, hidden_bit
        ) @ &m : res.`bke_protocol_consistency_failure
      ] = 0%r.
    + smt(mu_bounded ge0_mu).

    have Hsafe_failure_le :
      Pr[
        G.main_with_fixed_bit(
          users, group, kappa, membership, hidden_bit
        ) @ &m :
          res.`bke_safe /\
          res.`bke_protocol_consistency_failure
      ] <=
      Pr[
        G.main_with_fixed_bit(
          users, group, kappa, membership, hidden_bit
        ) @ &m : res.`bke_protocol_consistency_failure
      ].
    + by rewrite Pr[mu_sub].

    have Hsafe_failure_zero :
      Pr[
        G.main_with_fixed_bit(
          users, group, kappa, membership, hidden_bit
        ) @ &m :
          res.`bke_safe /\
          res.`bke_protocol_consistency_failure
      ] = 0%r.
    + smt(ge0_mu).

    have Hsafe_partition :
      Pr[
        G.main_with_fixed_bit(
          users, group, kappa, membership, hidden_bit
        ) @ &m : res.`bke_safe
      ] =
      Pr[
        G.main_with_fixed_bit(
          users, group, kappa, membership, hidden_bit
        ) @ &m :
          res.`bke_safe /\
          ! res.`bke_protocol_consistency_failure
      ] +
      Pr[
        G.main_with_fixed_bit(
          users, group, kappa, membership, hidden_bit
        ) @ &m :
          res.`bke_safe /\
          res.`bke_protocol_consistency_failure
      ].
    + have -> :
        Pr[
          G.main_with_fixed_bit(
            users, group, kappa, membership, hidden_bit
          ) @ &m : res.`bke_safe
        ] =
        Pr[
          G.main_with_fixed_bit(
            users, group, kappa, membership, hidden_bit
          ) @ &m :
            (res.`bke_safe /\
             ! res.`bke_protocol_consistency_failure) \/
            (res.`bke_safe /\
             res.`bke_protocol_consistency_failure)
        ].
      + by rewrite Pr[mu_eq] /#.
      by rewrite Pr[mu_disjoint] 1:/#.

    smt().
  qed.
end section BeeKemConsistencyBranchProjection.
