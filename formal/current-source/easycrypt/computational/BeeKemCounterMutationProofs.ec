require import AllCore List FSet.
require import BeeKemTypes BeeKemQueryLog BeeKemProtocol BeeKemSafety BeeKemKiGame.
require import BeeKemGameWitnesses BeeKemTheorem1Math.

(* Counter-loss mutations are evaluated from counters produced by the exact
   Figure 8 oracle code.  They are not independent theorem parameters. *)
op beekem_counter_first_target : beekem_user = BeeKemUser 720.
op beekem_counter_second_target : beekem_user = BeeKemUser 721.
op beekem_counter_initial_members : beekem_user fset =
  fset1 beekem_counter_first_target `|` fset1 beekem_counter_second_target.

module BeeKemCounterFactorAdversary(O : BEEKEM_KI_ORACLES) = {
  proc attack() : bool = {
    var created : bool;
    var updated : bool;
    var answer : beekem_secret_output;

    created <@ O.create_group(
      beekem_witness_user,
      beekem_counter_initial_members
    );
    updated <@ O.send_update(beekem_witness_user);
    answer <@ O.challenge(beekem_witness_user, BeeKemCounter 2);
    return created /\ updated /\
      answer = BeeSecretValue beekem_witness_real_secret;
  }
}.

module BeeKemCounterFactorGame =
  BeeKemKiGame(
    BeeKemCounterFactorAdversary,
    BeeKemWitnessProtocol
  ).

op beekem_drop_one_count (count : int) : int = count - 1.

lemma beekem_actual_counter_factors_are_nonzero :
  hoare [BeeKemCounterFactorGame.main_with_fixed_bit :
       users = [beekem_witness_user]
    /\ group = beekem_witness_group
    /\ kappa = 1
    /\ membership = beekem_witness_membership
    /\ hidden_bit = true
    ==>
       res.`bke_challenge_count = 1
    /\ res.`bke_member_addition_count = 2
    /\ beekem_is_ceil_log2 res.`bke_member_addition_count 1
    /\ beekem_is_ceil_log2
         (beekem_drop_one_count res.`bke_member_addition_count) 0
    /\ beekem_theorem1_loss res.`bke_challenge_count 1 = 1%r
    /\ beekem_theorem1_loss
         (beekem_drop_one_count res.`bke_challenge_count) 1 = 0%r
    /\ beekem_theorem1_loss res.`bke_challenge_count 0 = 0%r].
proof.
  proc; inline *.
  do ! (
    (rcondt ^if; first by auto=> />; cbv delta; rewrite ?inE ?elems_fset0 ?elems_fset1; cbv delta) ||
    (rcondf ^if; first by auto=> />; cbv delta; rewrite ?inE ?elems_fset0 ?elems_fset1; cbv delta) ||
    (rcondt ^while; first by auto=> />; cbv delta; rewrite ?inE ?elems_fset0 ?elems_fset1; cbv delta) ||
    (rcondf ^while; first by auto=> />; cbv delta; rewrite ?inE ?elems_fset0 ?elems_fset1; cbv delta)).
  auto=> />; cbv delta; rewrite ?inE ?elems_fset0 ?elems_fset1; cbv delta; rewrite ?inE; cbv delta.
  by rewrite -!cardE fcardU1 fcard1 in_fset1 /= (iteriS_rw 1) //= (iteri0 0) //=.
qed.

(* Rows 9 and 10 of the mutation matrix are deliberately separated below.
   Each theorem runs the same exact KI game and changes one derived theorem
   factor only: either the challenge count [c], or the member-addition count
   used to select [ceil(log2 n)]. *)
lemma mutation_drop_challenge_count_changes_theorem_factor :
  hoare [BeeKemCounterFactorGame.main_with_fixed_bit :
       users = [beekem_witness_user]
    /\ group = beekem_witness_group
    /\ kappa = 1
    /\ membership = beekem_witness_membership
    /\ hidden_bit = true
    ==>
       res.`bke_challenge_count = 1
    /\ beekem_theorem1_loss res.`bke_challenge_count 1 = 1%r
    /\ beekem_theorem1_loss
         (beekem_drop_one_count res.`bke_challenge_count) 1 = 0%r].
proof.
  conseq beekem_actual_counter_factors_are_nonzero => //.
qed.

lemma mutation_drop_addition_count_changes_logarithmic_factor :
  hoare [BeeKemCounterFactorGame.main_with_fixed_bit :
       users = [beekem_witness_user]
    /\ group = beekem_witness_group
    /\ kappa = 1
    /\ membership = beekem_witness_membership
    /\ hidden_bit = true
    ==>
       res.`bke_member_addition_count = 2
    /\ beekem_is_ceil_log2 res.`bke_member_addition_count 1
    /\ beekem_is_ceil_log2
         (beekem_drop_one_count res.`bke_member_addition_count) 0
    /\ beekem_theorem1_loss res.`bke_challenge_count 1 = 1%r
    /\ beekem_theorem1_loss res.`bke_challenge_count 0 = 0%r].
proof.
  conseq beekem_actual_counter_factors_are_nonzero => //.
qed.

(* The exact counter witness terminates with the asserted counters. *)
lemma beekem_actual_counter_factors_probability_one :
  phoare [BeeKemCounterFactorGame.main_with_fixed_bit :
       users = [beekem_witness_user]
    /\ group = beekem_witness_group
    /\ kappa = 1
    /\ membership = beekem_witness_membership
    /\ hidden_bit = true
    ==>
       res.`bke_challenge_count = 1
    /\ res.`bke_member_addition_count = 2
    /\ beekem_is_ceil_log2 res.`bke_member_addition_count 1
    /\ beekem_is_ceil_log2
         (beekem_drop_one_count res.`bke_member_addition_count) 0
    /\ beekem_theorem1_loss res.`bke_challenge_count 1 = 1%r
    /\ beekem_theorem1_loss
         (beekem_drop_one_count res.`bke_challenge_count) 1 = 0%r
    /\ beekem_theorem1_loss res.`bke_challenge_count 0 = 0%r] = 1%r.
proof.
  proc; inline *.
  do ! (
    (rcondt ^if; first by auto=> />; cbv delta; rewrite ?inE ?elems_fset0 ?elems_fset1; cbv delta) ||
    (rcondf ^if; first by auto=> />; cbv delta; rewrite ?inE ?elems_fset0 ?elems_fset1; cbv delta) ||
    (rcondt ^while; first by auto=> />; cbv delta; rewrite ?inE ?elems_fset0 ?elems_fset1; cbv delta) ||
    (rcondf ^while; first by auto=> />; cbv delta; rewrite ?inE ?elems_fset0 ?elems_fset1; cbv delta)).
  auto=> />; cbv delta; rewrite ?inE ?elems_fset0 ?elems_fset1; cbv delta; rewrite ?inE; cbv delta.
  by rewrite -!cardE fcardU1 fcard1 in_fset1 /= (iteriS_rw 1) //= (iteri0 0) //=.
qed.
