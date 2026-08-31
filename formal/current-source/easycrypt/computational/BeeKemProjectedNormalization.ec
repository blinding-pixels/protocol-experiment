require import AllCore List FSet.
require import BeeKemTypes BeeKemProtocol BeeKemKiGame.
require import BeeKemExecutableNormalization BeeKemFixedBitProjection.
require import BeeKemSafetyBranchProjection BeeKemConsistencyBranchProjection.
require import LivePrfGame.

(* Algebraic normalization of the two application one-events.  The real-root
   one-event is a correct guess when the hidden bit is true; on the random-root
   branch the KI win event is its complement inside safe mass one. *)
lemma beekem_projected_average_normalization
    (real_one_probability random_one_probability : real) :
  mdprf_fixed_bit_advantage
    real_one_probability random_one_probability / 2%r =
  beekem_normalized_ki_advantage
    ((real_one_probability +
      (1%r - random_one_probability)) / 2%r).
proof.
  rewrite /mdprf_fixed_bit_advantage /beekem_normalized_ki_advantage.
  case (random_one_probability <= real_one_probability);
  case (1%r / 2%r <=
        (real_one_probability + (1%r - random_one_probability)) / 2%r);
  smt().
qed.

section BeeKemProjectedNormalization.
  declare module A <: BEEKEM_KI_ADVERSARY.
  declare module P <: BEEKEM_PROTOCOL_ALGORITHMS.

  module G = BeeKemKiGame(A, P).

  (* This is the exact bridge needed by the application hybrid: the normalized
     distance between its two fixed-bit one-events is the imported KI game's
     normalized hidden-bit advantage.  The only premises are the explicit
     theorem-boundary masses used by the two branch characterizations. *)
  lemma beekem_projected_fixed_bit_advantage_exactly_normalized_ki
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
        users, group, kappa, membership, false
      ) @ &m : res.`bke_safe
    ] = 1%r =>
    mdprf_fixed_bit_advantage
      (Pr[
         G.main_with_fixed_bit(
           users, group, kappa, membership, true
         ) @ &m :
           res.`bke_safe /\
           ! res.`bke_protocol_consistency_failure /\
           res.`bke_adversary_guess
       ])
      (Pr[
         G.main_with_fixed_bit(
           users, group, kappa, membership, false
         ) @ &m :
           res.`bke_safe /\
           ! res.`bke_protocol_consistency_failure /\
           res.`bke_adversary_guess
       ]) / 2%r =
    beekem_normalized_ki_advantage
      (Pr[
         G.main(users, group, kappa, membership) @ &m : res
       ]).
  proof.
    move=> Hreal Hrandom.
    have Htrue :=
      beekem_fixed_true_win_probability_is_projected
        A P &m users group kappa membership Hreal.
    have Hfalse :=
      beekem_fixed_false_win_probability_is_projected_complement
        A P &m users group kappa membership Hrandom.
    rewrite
      (beekem_sampled_win_probability_is_fixed_bit_average
         A P &m users group kappa membership)
      Htrue Hfalse.
    exact
      (beekem_projected_average_normalization
         (Pr[
            G.main_with_fixed_bit(
              users, group, kappa, membership, true
            ) @ &m :
              res.`bke_safe /\
              ! res.`bke_protocol_consistency_failure /\
              res.`bke_adversary_guess
          ])
         (Pr[
            G.main_with_fixed_bit(
              users, group, kappa, membership, false
            ) @ &m :
              res.`bke_safe /\
              ! res.`bke_protocol_consistency_failure /\
              res.`bke_adversary_guess
          ])).
  qed.

  (* The random-branch premise above is not independent.  The imported
     theorem's sampled all-safe condition yields it through the executable
     fair-bit safety decomposition. *)
  lemma beekem_projected_fixed_bit_advantage_from_sampled_safe
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
      G.main_with_evidence(users, group, kappa, membership) @ &m :
        res.`bke_safe
    ] = 1%r =>
    mdprf_fixed_bit_advantage
      (Pr[
         G.main_with_fixed_bit(
           users, group, kappa, membership, true
         ) @ &m :
           res.`bke_safe /\
           ! res.`bke_protocol_consistency_failure /\
           res.`bke_adversary_guess
       ])
      (Pr[
         G.main_with_fixed_bit(
           users, group, kappa, membership, false
         ) @ &m :
           res.`bke_safe /\
           ! res.`bke_protocol_consistency_failure /\
           res.`bke_adversary_guess
       ]) / 2%r =
    beekem_normalized_ki_advantage
      (Pr[
         G.main(users, group, kappa, membership) @ &m : res
       ]).
  proof.
    move=> Hreal Hsampled.
    have Hfixed :=
      beekem_sampled_safe_one_implies_fixed_safe_one
        A P &m users group kappa membership Hsampled.
    elim Hfixed => Htrue Hfalse.
    exact
      (beekem_projected_fixed_bit_advantage_exactly_normalized_ki
         A P &m users group kappa membership Hreal Hfalse).
  qed.

  (* The remaining real-branch conjunction is likewise derived rather than
     assumed.  Sampled all-safe mass gives fixed-bit safety; the only additional
     boundary is probability-one protocol consistency for the concrete paper
     implementation on the real branch. *)
  lemma beekem_projected_fixed_bit_advantage_from_sampled_safe_and_consistency
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
      ) @ &m : ! res.`bke_protocol_consistency_failure
    ] = 1%r =>
    mdprf_fixed_bit_advantage
      (Pr[
         G.main_with_fixed_bit(
           users, group, kappa, membership, true
         ) @ &m :
           res.`bke_safe /\
           ! res.`bke_protocol_consistency_failure /\
           res.`bke_adversary_guess
       ])
      (Pr[
         G.main_with_fixed_bit(
           users, group, kappa, membership, false
         ) @ &m :
           res.`bke_safe /\
           ! res.`bke_protocol_consistency_failure /\
           res.`bke_adversary_guess
       ]) / 2%r =
    beekem_normalized_ki_advantage
      (Pr[
         G.main(users, group, kappa, membership) @ &m : res
       ]).
  proof.
    move=> Hsampled Hconsistent.
    have Hfixed :=
      beekem_sampled_safe_one_implies_fixed_safe_one
        A P &m users group kappa membership Hsampled.
    elim Hfixed => Htrue Hfalse.
    have Hreal :=
      beekem_fixed_safe_and_consistent_probability_one
        A P &m users group kappa membership true Htrue Hconsistent.
    exact
      (beekem_projected_fixed_bit_advantage_from_sampled_safe
         A P &m users group kappa membership Hreal Hsampled).
  qed.
end section BeeKemProjectedNormalization.
