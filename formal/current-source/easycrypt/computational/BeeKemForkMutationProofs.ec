require import AllCore List FSet.
require import BeeKemTypes BeeKemQueryLog BeeKemProtocol BeeKemSafety.
require import BeeKemKiGame BeeKemGameWitnesses BeeKemSafetyMutations.
require import BeeKemMutationGameProofs BeeKemForkGameWitnesses.

module BeeKemCfsForkMutationGame =
  BeeKemSafetyMutationGame(
    BeeKemCfsForkExposureAdversary,
    BeeKemForkWitnessProtocol
  ).

module BeeKemCausalAncestryMutationGame =
  BeeKemSafetyMutationGame(
    BeeKemCausalAncestryExposureAdversary,
    BeeKemForkWitnessProtocol
  ).

lemma mutation_cfs_chain_reaches_actual_ki_game :
  hoare [BeeKemCfsForkMutationGame.main_with_fixed_mutation :
       users = [beekem_witness_user]
    /\ group = beekem_witness_group
    /\ kappa = 2
    /\ membership = beekem_witness_membership
    /\ hidden_bit = true
    /\ mutation = BeeMutationDropCfsUpdateChain
    ==>
       res.`bmge_hidden_bit
    /\ res.`bmge_adversary_guess
    /\ ! res.`bmge_protocol_consistency_failure
    /\ res.`bmge_challenge_count = 1
    /\ res.`bmge_member_addition_count = 0
    /\ ! res.`bmge_exact_safe
    /\ ! res.`bmge_exact_win
    /\ res.`bmge_mutated_safe
    /\ res.`bmge_mutated_win].
proof.
  proc; inline *.
  do ! (
    (rcondt ^if; first by auto=> />; cbv delta; rewrite ?inE ?elems_fset0 ?elems_fset1; cbv delta; rewrite ?inE ?elems_fset0 ?elems_fset1; cbv delta) ||
    (rcondf ^if; first by auto=> />; cbv delta; rewrite ?inE ?elems_fset0 ?elems_fset1; cbv delta; rewrite ?inE ?elems_fset0 ?elems_fset1; cbv delta) ||
    (rcondt ^while; first by auto=> />; cbv delta; rewrite ?inE ?elems_fset0 ?elems_fset1; cbv delta; rewrite ?inE ?elems_fset0 ?elems_fset1; cbv delta) ||
    (rcondf ^while; first by auto=> />; cbv delta; rewrite ?inE ?elems_fset0 ?elems_fset1; cbv delta; rewrite ?inE ?elems_fset0 ?elems_fset1; cbv delta)).
  by auto=> />; cbv delta; rewrite ?inE ?elems_fset0 ?elems_fset1; cbv delta; rewrite ?inE ?elems_fset0 ?elems_fset1; cbv delta; rewrite ?inE ?elems_fset0 ?elems_fset1; cbv delta.
qed.

lemma mutation_ignore_ancestry_reaches_actual_ki_game :
  hoare [BeeKemCausalAncestryMutationGame.main_with_fixed_mutation :
       users = [beekem_witness_user]
    /\ group = beekem_witness_group
    /\ kappa = 1
    /\ membership = beekem_witness_membership
    /\ hidden_bit = true
    /\ mutation = BeeMutationIgnoreCausalAncestry
    ==>
       res.`bmge_hidden_bit
    /\ res.`bmge_adversary_guess
    /\ ! res.`bmge_protocol_consistency_failure
    /\ res.`bmge_challenge_count = 1
    /\ res.`bmge_member_addition_count = 1
    /\ ! res.`bmge_exact_safe
    /\ ! res.`bmge_exact_win
    /\ res.`bmge_mutated_safe
    /\ res.`bmge_mutated_win].
proof.
  proc; inline *.
  do ! (
    (rcondt ^if; first by auto=> />; cbv delta; rewrite ?inE ?elems_fset0 ?elems_fset1; cbv delta; rewrite ?inE ?elems_fset0 ?elems_fset1; cbv delta) ||
    (rcondf ^if; first by auto=> />; cbv delta; rewrite ?inE ?elems_fset0 ?elems_fset1; cbv delta; rewrite ?inE ?elems_fset0 ?elems_fset1; cbv delta) ||
    (rcondt ^while; first by auto=> />; cbv delta; rewrite ?inE ?elems_fset0 ?elems_fset1; cbv delta; rewrite ?inE ?elems_fset0 ?elems_fset1; cbv delta) ||
    (rcondf ^while; first by auto=> />; cbv delta; rewrite ?inE ?elems_fset0 ?elems_fset1; cbv delta; rewrite ?inE ?elems_fset0 ?elems_fset1; cbv delta)).
  auto=> />; cbv delta; rewrite ?inE ?elems_fset0 ?elems_fset1; cbv delta; rewrite ?inE ?elems_fset0 ?elems_fset1; cbv delta; rewrite ?inE ?elems_fset0 ?elems_fset1; cbv delta.
  smt(fsetP in_fset0 in_fset1).
qed.

(* Terminating versions of the same executable controls, not extra assumptions. *)
lemma mutation_cfs_chain_reaches_actual_ki_game_probability_one :
  phoare [BeeKemCfsForkMutationGame.main_with_fixed_mutation :
       users = [beekem_witness_user]
    /\ group = beekem_witness_group
    /\ kappa = 2
    /\ membership = beekem_witness_membership
    /\ hidden_bit = true
    /\ mutation = BeeMutationDropCfsUpdateChain
    ==>
       res.`bmge_hidden_bit
    /\ res.`bmge_adversary_guess
    /\ ! res.`bmge_protocol_consistency_failure
    /\ res.`bmge_challenge_count = 1
    /\ res.`bmge_member_addition_count = 0
    /\ ! res.`bmge_exact_safe
    /\ ! res.`bmge_exact_win
    /\ res.`bmge_mutated_safe
    /\ res.`bmge_mutated_win] = 1%r.
proof.
  proc; inline *.
  do ! (
    (rcondt ^if; first by auto=> />; cbv delta; rewrite ?inE ?elems_fset0 ?elems_fset1; cbv delta; rewrite ?inE ?elems_fset0 ?elems_fset1; cbv delta) ||
    (rcondf ^if; first by auto=> />; cbv delta; rewrite ?inE ?elems_fset0 ?elems_fset1; cbv delta; rewrite ?inE ?elems_fset0 ?elems_fset1; cbv delta) ||
    (rcondt ^while; first by auto=> />; cbv delta; rewrite ?inE ?elems_fset0 ?elems_fset1; cbv delta; rewrite ?inE ?elems_fset0 ?elems_fset1; cbv delta) ||
    (rcondf ^while; first by auto=> />; cbv delta; rewrite ?inE ?elems_fset0 ?elems_fset1; cbv delta; rewrite ?inE ?elems_fset0 ?elems_fset1; cbv delta)).
  by auto=> />; cbv delta; rewrite ?inE ?elems_fset0 ?elems_fset1; cbv delta; rewrite ?inE ?elems_fset0 ?elems_fset1; cbv delta; rewrite ?inE ?elems_fset0 ?elems_fset1; cbv delta.
qed.

lemma mutation_ignore_ancestry_reaches_actual_ki_game_probability_one :
  phoare [BeeKemCausalAncestryMutationGame.main_with_fixed_mutation :
       users = [beekem_witness_user]
    /\ group = beekem_witness_group
    /\ kappa = 1
    /\ membership = beekem_witness_membership
    /\ hidden_bit = true
    /\ mutation = BeeMutationIgnoreCausalAncestry
    ==>
       res.`bmge_hidden_bit
    /\ res.`bmge_adversary_guess
    /\ ! res.`bmge_protocol_consistency_failure
    /\ res.`bmge_challenge_count = 1
    /\ res.`bmge_member_addition_count = 1
    /\ ! res.`bmge_exact_safe
    /\ ! res.`bmge_exact_win
    /\ res.`bmge_mutated_safe
    /\ res.`bmge_mutated_win] = 1%r.
proof.
  proc; inline *.
  do ! (
    (rcondt ^if; first by auto=> />; cbv delta; rewrite ?inE ?elems_fset0 ?elems_fset1; cbv delta; rewrite ?inE ?elems_fset0 ?elems_fset1; cbv delta) ||
    (rcondf ^if; first by auto=> />; cbv delta; rewrite ?inE ?elems_fset0 ?elems_fset1; cbv delta; rewrite ?inE ?elems_fset0 ?elems_fset1; cbv delta) ||
    (rcondt ^while; first by auto=> />; cbv delta; rewrite ?inE ?elems_fset0 ?elems_fset1; cbv delta; rewrite ?inE ?elems_fset0 ?elems_fset1; cbv delta) ||
    (rcondf ^while; first by auto=> />; cbv delta; rewrite ?inE ?elems_fset0 ?elems_fset1; cbv delta; rewrite ?inE ?elems_fset0 ?elems_fset1; cbv delta)).
  auto=> />; cbv delta; rewrite ?inE ?elems_fset0 ?elems_fset1; cbv delta; rewrite ?inE ?elems_fset0 ?elems_fset1; cbv delta; rewrite ?inE ?elems_fset0 ?elems_fset1; cbv delta.
  smt(fsetP in_fset0 in_fset1).
qed.
