require import AllCore List FSet Distr.
require import BeeKemTypes BeeKemQueryLog BeeKemProtocol BeeKemSafety.
require import BeeKemKiGame BeeKemGameWitnesses BeeKemMutationGameProofs.

(* Use the exact Figure-8 game and the existing FSU exposure adversary.  The
   trace executes Create -> Update -> Challenge -> Compromise.  Its challenge
   is real and counted, but the complete authoritative log is unsafe for every
   hidden bit, so the exact game must lose rather than gain half an advantage. *)
module BeeKemUnsafeNormalizationGame =
  BeeKemKiGame(
    BeeKemFsuExposureAdversary,
    BeeKemWitnessProtocol
  ).

lemma beekem_unsafe_normalization_fixed_bit_loses :
  hoare [BeeKemUnsafeNormalizationGame.main_with_fixed_bit :
       users = [beekem_witness_user]
    /\ group = beekem_witness_group
    /\ kappa = 1
    /\ membership = beekem_witness_membership
    ==>
       res.`bke_challenge_count = 1
    /\ ! res.`bke_safe
    /\ ! res.`bke_win].
proof.
  proc; case (hidden_bit).
  + inline *.
  rcondt ^while; first by auto.
  rcondf ^while; first by auto.
  rcondf ^if; first by auto=> />; cbv delta; rewrite ?inE ?elems_fset0 ?elems_fset1; cbv delta.
  rcondt ^if; first by auto=> />; cbv delta; rewrite ?inE ?elems_fset0 ?elems_fset1; cbv delta.
  rcondf ^if; first by auto=> />; cbv delta; rewrite ?inE ?elems_fset0 ?elems_fset1; cbv delta.
  rcondf ^if; first by auto=> />; cbv delta; rewrite ?inE ?elems_fset0 ?elems_fset1; cbv delta.
  rcondf ^if; first by auto=> />; cbv delta; rewrite ?inE ?elems_fset0 ?elems_fset1; cbv delta.
  rcondt ^if; first by auto=> />; cbv delta; rewrite ?inE ?elems_fset0 ?elems_fset1; cbv delta.
  rcondf ^if; first by auto=> />; cbv delta; rewrite ?inE ?elems_fset0 ?elems_fset1; cbv delta.
  rcondf ^if; first by auto=> />; cbv delta; rewrite ?inE ?elems_fset0 ?elems_fset1; cbv delta.
  rcondt ^if; first by auto=> />; cbv delta; rewrite ?inE ?elems_fset0 ?elems_fset1; cbv delta.
  rcondf ^if; first by auto=> />; cbv delta; rewrite ?inE ?elems_fset0 ?elems_fset1; cbv delta.
  rcondf ^while; first by auto=> />; cbv delta; rewrite ?inE ?elems_fset0 ?elems_fset1; cbv delta.
  rcondt ^while; first by auto=> />; cbv delta; rewrite ?inE ?elems_fset0 ?elems_fset1; cbv delta.
  rcondf ^while; first by auto=> />; cbv delta; rewrite ?inE ?elems_fset0 ?elems_fset1; cbv delta.
  rcondt ^if; first by auto=> />; cbv delta; rewrite ?inE ?elems_fset0 ?elems_fset1; cbv delta.
  rcondt ^if; first by auto=> />; cbv delta; rewrite ?inE ?elems_fset0 ?elems_fset1; cbv delta.
  rcondf ^if; first by auto=> />; cbv delta; rewrite ?inE ?elems_fset0 ?elems_fset1; cbv delta.
  rcondt ^if; first by auto=> />; cbv delta; rewrite ?inE ?elems_fset0 ?elems_fset1; cbv delta.
  rcondf ^if; first by auto=> />; cbv delta; rewrite ?inE ?elems_fset0 ?elems_fset1; cbv delta.
  rcondf ^if; first by auto=> />; cbv delta; rewrite ?inE ?elems_fset0 ?elems_fset1; cbv delta.
  rcondt ^if; first by auto=> />; cbv delta; rewrite ?inE ?elems_fset0 ?elems_fset1; cbv delta.
  rcondf ^if; first by auto=> />; cbv delta; rewrite ?inE ?elems_fset0 ?elems_fset1; cbv delta.
  rcondf ^while; first by auto=> />; cbv delta; rewrite ?inE ?elems_fset0 ?elems_fset1; cbv delta.
  rcondt ^if; first by auto=> />; cbv delta; rewrite ?inE ?elems_fset0 ?elems_fset1; cbv delta.
  rcondf ^if; first by auto=> />; cbv delta; rewrite ?inE ?elems_fset0 ?elems_fset1; cbv delta.
  rcondf ^if; first by auto=> />; cbv delta; rewrite ?inE ?elems_fset0 ?elems_fset1; cbv delta.
  rcondt ^if; first by auto=> />; cbv delta; rewrite ?inE ?elems_fset0 ?elems_fset1; cbv delta.
  rcondt ^if; first by auto=> />; cbv delta; rewrite ?inE ?elems_fset0 ?elems_fset1; cbv delta.
  rcondt ^if; first by auto=> />; cbv delta; rewrite ?inE ?elems_fset0 ?elems_fset1; cbv delta.
  rcondt ^if; first by auto=> />; cbv delta; rewrite ?inE ?elems_fset0 ?elems_fset1; cbv delta.
  auto=> />.
  cbv delta; rewrite ?inE ?elems_fset0 ?elems_fset1; cbv delta.
  by rewrite !inE.
  + inline *.
  rcondt ^while; first by auto.
  rcondf ^while; first by auto.
  rcondf ^if; first by auto=> />; cbv delta; rewrite ?inE ?elems_fset0 ?elems_fset1; cbv delta.
  rcondt ^if; first by auto=> />; cbv delta; rewrite ?inE ?elems_fset0 ?elems_fset1; cbv delta.
  rcondf ^if; first by auto=> />; cbv delta; rewrite ?inE ?elems_fset0 ?elems_fset1; cbv delta.
  rcondf ^if; first by auto=> />; cbv delta; rewrite ?inE ?elems_fset0 ?elems_fset1; cbv delta.
  rcondf ^if; first by auto=> />; cbv delta; rewrite ?inE ?elems_fset0 ?elems_fset1; cbv delta.
  rcondt ^if; first by auto=> />; cbv delta; rewrite ?inE ?elems_fset0 ?elems_fset1; cbv delta.
  rcondf ^if; first by auto=> />; cbv delta; rewrite ?inE ?elems_fset0 ?elems_fset1; cbv delta.
  rcondf ^if; first by auto=> />; cbv delta; rewrite ?inE ?elems_fset0 ?elems_fset1; cbv delta.
  rcondt ^if; first by auto=> />; cbv delta; rewrite ?inE ?elems_fset0 ?elems_fset1; cbv delta.
  rcondf ^if; first by auto=> />; cbv delta; rewrite ?inE ?elems_fset0 ?elems_fset1; cbv delta.
  rcondf ^while; first by auto=> />; cbv delta; rewrite ?inE ?elems_fset0 ?elems_fset1; cbv delta.
  rcondt ^while; first by auto=> />; cbv delta; rewrite ?inE ?elems_fset0 ?elems_fset1; cbv delta.
  rcondf ^while; first by auto=> />; cbv delta; rewrite ?inE ?elems_fset0 ?elems_fset1; cbv delta.
  rcondt ^if; first by auto=> />; cbv delta; rewrite ?inE ?elems_fset0 ?elems_fset1; cbv delta.
  rcondt ^if; first by auto=> />; cbv delta; rewrite ?inE ?elems_fset0 ?elems_fset1; cbv delta.
  rcondf ^if; first by auto=> />; cbv delta; rewrite ?inE ?elems_fset0 ?elems_fset1; cbv delta.
  rcondt ^if; first by auto=> />; cbv delta; rewrite ?inE ?elems_fset0 ?elems_fset1; cbv delta.
  rcondf ^if; first by auto=> />; cbv delta; rewrite ?inE ?elems_fset0 ?elems_fset1; cbv delta.
  rcondf ^if; first by auto=> />; cbv delta; rewrite ?inE ?elems_fset0 ?elems_fset1; cbv delta.
  rcondt ^if; first by auto=> />; cbv delta; rewrite ?inE ?elems_fset0 ?elems_fset1; cbv delta.
  rcondf ^if; first by auto=> />; cbv delta; rewrite ?inE ?elems_fset0 ?elems_fset1; cbv delta.
  rcondf ^while; first by auto=> />; cbv delta; rewrite ?inE ?elems_fset0 ?elems_fset1; cbv delta.
  rcondt ^if; first by auto=> />; cbv delta; rewrite ?inE ?elems_fset0 ?elems_fset1; cbv delta.
  rcondf ^if; first by auto=> />; cbv delta; rewrite ?inE ?elems_fset0 ?elems_fset1; cbv delta.
  rcondf ^if; first by auto=> />; cbv delta; rewrite ?inE ?elems_fset0 ?elems_fset1; cbv delta.
  rcondt ^if; first by auto=> />; cbv delta; rewrite ?inE ?elems_fset0 ?elems_fset1; cbv delta.
  rcondt ^if; first by auto=> />; cbv delta; rewrite ?inE ?elems_fset0 ?elems_fset1; cbv delta.
  rcondf ^if; first by auto=> />; cbv delta; rewrite ?inE ?elems_fset0 ?elems_fset1; cbv delta.
  rcondt ^if; first by auto=> />; cbv delta; rewrite ?inE ?elems_fset0 ?elems_fset1; cbv delta.
  rcondt ^if; first by auto=> />; cbv delta; rewrite ?inE ?elems_fset0 ?elems_fset1; cbv delta.
  auto=> />.
  cbv delta; rewrite ?inE ?elems_fset0 ?elems_fset1; cbv delta.
  by rewrite !inE.
qed.

lemma beekem_unsafe_normalization_sampled_game_loses :
  hoare [BeeKemUnsafeNormalizationGame.main_with_evidence :
       users = [beekem_witness_user]
    /\ group = beekem_witness_group
    /\ kappa = 1
    /\ membership = beekem_witness_membership
    ==>
       res.`bke_challenge_count = 1
    /\ ! res.`bke_safe
    /\ ! res.`bke_win].
proof.
  proc.
  call beekem_unsafe_normalization_fixed_bit_loses.
  auto.
qed.

lemma beekem_unsafe_normalization_main_never_wins :
  hoare [BeeKemUnsafeNormalizationGame.main :
       users = [beekem_witness_user]
    /\ group = beekem_witness_group
    /\ kappa = 1
    /\ membership = beekem_witness_membership
    ==>
       ! res].
proof.
  proc.
  call beekem_unsafe_normalization_sampled_game_loses.
  auto.
qed.

lemma beekem_unsafe_normalization_win_probability_zero &m :
  Pr[
    BeeKemUnsafeNormalizationGame.main(
      [beekem_witness_user],
      beekem_witness_group,
      1,
      beekem_witness_membership
    ) @ &m : res
  ] = 0%r.
proof.
  byphoare
    (_ :
       users = [beekem_witness_user]
    /\ group = beekem_witness_group
    /\ kappa = 1
    /\ membership = beekem_witness_membership
    ==> res) => //=.
  hoare.
  exact beekem_unsafe_normalization_main_never_wins.
qed.

lemma beekem_unsafe_normalization_safe_probability_zero &m :
  Pr[
    BeeKemUnsafeNormalizationGame.main_with_evidence(
      [beekem_witness_user],
      beekem_witness_group,
      1,
      beekem_witness_membership
    ) @ &m : res.`bke_safe
  ] = 0%r.
proof.
  byphoare
    (_ :
       users = [beekem_witness_user]
    /\ group = beekem_witness_group
    /\ kappa = 1
    /\ membership = beekem_witness_membership
    ==> res.`bke_safe) => //=.
  hoare.
  conseq beekem_unsafe_normalization_sampled_game_loses => //.
qed.

(* This is the exact old bug: centering the aborted win probability around an
   unconditional half gives a spurious half advantage. *)
lemma beekem_unsafe_trace_old_normalization_is_spurious_half &m :
  beekem_normalized_ki_advantage
    (Pr[
       BeeKemUnsafeNormalizationGame.main(
         [beekem_witness_user],
         beekem_witness_group,
         1,
         beekem_witness_membership
       ) @ &m : res
     ]) = 1%r / 2%r.
proof.
  rewrite beekem_unsafe_normalization_win_probability_zero.
  rewrite /beekem_normalized_ki_advantage.
  by smt().
qed.

lemma beekem_unsafe_trace_safe_mass_advantage_zero &m :
  beekem_safe_mass_normalized_ki_advantage
    (Pr[
       BeeKemUnsafeNormalizationGame.main(
         [beekem_witness_user],
         beekem_witness_group,
         1,
         beekem_witness_membership
       ) @ &m : res
     ])
    (Pr[
       BeeKemUnsafeNormalizationGame.main_with_evidence(
         [beekem_witness_user],
         beekem_witness_group,
         1,
         beekem_witness_membership
       ) @ &m : res.`bke_safe
     ]) = 0%r.
proof.
  rewrite beekem_unsafe_normalization_win_probability_zero
    beekem_unsafe_normalization_safe_probability_zero.
  exact beekem_safe_mass_normalization_zero.
qed.

(* The same executable unsafe trace cannot discharge the imported theorem's
   all-safe side condition.  Final application composition must prove that side
   condition from the authoritative adapter and complete query log. *)
lemma beekem_unsafe_trace_rejected_by_all_safe_boundary &m :
  Pr[
    BeeKemUnsafeNormalizationGame.main_with_evidence(
      [beekem_witness_user],
      beekem_witness_group,
      1,
      beekem_witness_membership
    ) @ &m : res.`bke_safe
  ] <> 1%r.
proof.
  rewrite beekem_unsafe_normalization_safe_probability_zero.
  by smt().
qed.
