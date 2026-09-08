require import AllCore List FSet.
require import BeeKemTypes BeeKemQueryLog BeeKemProtocol BeeKemSafety.
require import BeeKemKiGame BeeKemGameWitnesses BeeKemSafetyMutations.

(* The mutation harness first executes the exact KI-DCGKA game, including its
   real oracle state and query log.  It then changes only the named final safety
   predicate and recomputes the win bit through [beekem_ki_final_win]. *)
type beekem_mutation_game_evidence = {
  bmge_hidden_bit : bool;
  bmge_adversary_guess : bool;
  bmge_protocol_consistency_failure : bool;
  bmge_challenge_count : int;
  bmge_member_addition_count : int;
  bmge_exact_safe : bool;
  bmge_exact_win : bool;
  bmge_mutated_safe : bool;
  bmge_mutated_win : bool
}.

module BeeKemSafetyMutationGame(
  A : BEEKEM_KI_ADVERSARY,
  P : BEEKEM_PROTOCOL_ALGORITHMS
) = {
  module Exact = BeeKemKiGame(A, P)

  proc main_with_fixed_mutation(
    users : beekem_user list,
    group : beekem_group,
    kappa : int,
    membership : beekem_dgm,
    hidden_bit : bool,
    mutation : beekem_safety_mutation
  ) : beekem_mutation_game_evidence = {
    var exact_evidence : beekem_ki_evidence;
    var mutated_safe : bool;
    var mutated_win : bool;

    exact_evidence <@ Exact.main_with_fixed_bit(
      users, group, kappa, membership, hidden_bit
    );
    mutated_safe <- bee_safe_kappa_mutated
      mutation
      kappa
      Exact.O.Environment.state.`bps_operations
      Exact.O.Environment.query_log;
    mutated_win <- beekem_ki_final_win
      mutated_safe
      exact_evidence.`bke_protocol_consistency_failure
      exact_evidence.`bke_adversary_guess
      hidden_bit;

    return
      {| bmge_hidden_bit = exact_evidence.`bke_hidden_bit;
         bmge_adversary_guess = exact_evidence.`bke_adversary_guess;
         bmge_protocol_consistency_failure =
           exact_evidence.`bke_protocol_consistency_failure;
         bmge_challenge_count = exact_evidence.`bke_challenge_count;
         bmge_member_addition_count = exact_evidence.`bke_member_addition_count;
         bmge_exact_safe = exact_evidence.`bke_safe;
         bmge_exact_win = exact_evidence.`bke_win;
         bmge_mutated_safe = mutated_safe;
         bmge_mutated_win = mutated_win |};
  }
}.

module BeeKemFsuExposureAdversary(O : BEEKEM_KI_ORACLES) = {
  proc attack() : bool = {
    var created : bool;
    var updated : bool;
    var answer : beekem_secret_output;
    var compromised : beekem_member_state option;

    created <@ O.create_group(beekem_witness_user, fset0);
    updated <@ O.send_update(beekem_witness_user);
    answer <@ O.challenge(beekem_witness_user, BeeKemCounter 2);
    compromised <@ O.compromise(beekem_witness_user);
    return created /\ updated /\ compromised <> None /\
      answer = BeeSecretValue beekem_witness_real_secret;
  }
}.

module BeeKemPcsExposureAdversary(O : BEEKEM_KI_ORACLES) = {
  proc attack() : bool = {
    var created : bool;
    var updated : bool;
    var compromised : beekem_member_state option;
    var answer : beekem_secret_output;

    created <@ O.create_group(beekem_witness_user, fset0);
    updated <@ O.send_update(beekem_witness_user);
    compromised <@ O.compromise(beekem_witness_user);
    answer <@ O.challenge(beekem_witness_user, BeeKemCounter 2);
    return created /\ updated /\ compromised <> None /\
      answer = BeeSecretValue beekem_witness_real_secret;
  }
}.

module BeeKemFsuExposureMutationGame =
  BeeKemSafetyMutationGame(
    BeeKemFsuExposureAdversary,
    BeeKemWitnessProtocol
  ).

module BeeKemPcsExposureMutationGame =
  BeeKemSafetyMutationGame(
    BeeKemPcsExposureAdversary,
    BeeKemWitnessProtocol
  ).

lemma mutation_fsu_chain_reaches_actual_ki_game :
  hoare [BeeKemFsuExposureMutationGame.main_with_fixed_mutation :
       users = [beekem_witness_user]
    /\ group = beekem_witness_group
    /\ kappa = 1
    /\ membership = beekem_witness_membership
    /\ hidden_bit = true
    /\ mutation = BeeMutationDropFsuUpdateChain
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
qed.

lemma mutation_pcs_update_reaches_actual_ki_game :
  hoare [BeeKemPcsExposureMutationGame.main_with_fixed_mutation :
       users = [beekem_witness_user]
    /\ group = beekem_witness_group
    /\ kappa = 1
    /\ membership = beekem_witness_membership
    /\ hidden_bit = true
    /\ mutation = BeeMutationDropPcsHealingUpdate
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
  rcondt ^if; first by auto=> />; cbv delta; rewrite ?inE ?elems_fset0 ?elems_fset1; cbv delta.
  rcondf ^if; first by auto=> />; cbv delta; rewrite ?inE ?elems_fset0 ?elems_fset1; cbv delta.
  rcondf ^if; first by auto=> />; cbv delta; rewrite ?inE ?elems_fset0 ?elems_fset1; cbv delta.
  rcondt ^if; first by auto=> />; cbv delta; rewrite ?inE ?elems_fset0 ?elems_fset1; cbv delta.
  rcondt ^if; first by auto=> />; cbv delta; rewrite ?inE ?elems_fset0 ?elems_fset1; cbv delta.
  rcondt ^if; first by auto=> />; cbv delta; rewrite ?inE ?elems_fset0 ?elems_fset1; cbv delta.
  auto=> />.
  cbv delta; rewrite ?inE ?elems_fset0 ?elems_fset1; cbv delta.
  by rewrite !inE.
qed.

lemma mutation_compromise_log_reaches_actual_ki_game :
  hoare [BeeKemFsuExposureMutationGame.main_with_fixed_mutation :
       users = [beekem_witness_user]
    /\ group = beekem_witness_group
    /\ kappa = 1
    /\ membership = beekem_witness_membership
    /\ hidden_bit = true
    /\ mutation = BeeMutationIgnoreCompromiseLog
    ==>
       res.`bmge_hidden_bit
    /\ res.`bmge_adversary_guess
    /\ ! res.`bmge_protocol_consistency_failure
    /\ res.`bmge_challenge_count = 1
    /\ ! res.`bmge_exact_safe
    /\ ! res.`bmge_exact_win
    /\ res.`bmge_mutated_safe
    /\ res.`bmge_mutated_win].
proof.
  proc; inline *.
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
qed.
