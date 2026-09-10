require import AllCore List FSet.
require import BeeKemTypes BeeKemQueryLog BeeKemProtocol BeeKemSafety BeeKemKiGame.
require import BeeKemGameWitnesses.

(* The paper's c and n factors are not free parameters in the executable game:
   they are the counters maintained by successful CHALLENGE and member-addition
   transitions.  These witnesses drive the actual oracle environment and pin
   both counters to concrete values. *)

op beekem_witness_add_target : beekem_user = BeeKemUser 711.

module BeeKemWitnessAdditionCounterAdversary(O : BEEKEM_KI_ORACLES) = {
  proc attack() : bool = {
    var created : bool;
    var added : bool;

    created <@ O.create_group(beekem_witness_user, fset0);
    added <@ O.add_member(beekem_witness_user, beekem_witness_add_target);
    return false;
  }
}.

module BeeKemWitnessAdditionCounterGame =
  BeeKemKiGame(
    BeeKemWitnessAdditionCounterAdversary,
    BeeKemWitnessProtocol
  ).

lemma beekem_actual_challenge_counter_reaches_one :
  hoare [BeeKemWitnessGame.main_with_fixed_bit :
       users = [beekem_witness_user]
    /\ group = beekem_witness_group
    /\ kappa = 1
    /\ membership = beekem_witness_membership
    /\ hidden_bit = true
    ==>
       res.`bke_challenge_count = 1
    /\ res.`bke_member_addition_count = 0].
proof.
  conseq beekem_witness_real_branch_reachable => //.
qed.

lemma beekem_actual_addition_counter_reaches_one :
  hoare [BeeKemWitnessAdditionCounterGame.main_with_fixed_bit :
       users = [beekem_witness_user]
    /\ group = beekem_witness_group
    /\ kappa = 1
    /\ membership = beekem_witness_membership
    /\ hidden_bit = false
    ==>
       ! res.`bke_hidden_bit
    /\ ! res.`bke_adversary_guess
    /\ res.`bke_safe
    /\ ! res.`bke_protocol_consistency_failure
    /\ res.`bke_challenge_count = 0
    /\ res.`bke_member_addition_count = 1
    /\ res.`bke_win].
proof.
  proc; inline *.
  do ! (
    (rcondt ^if; first by auto=> />; cbv delta; rewrite ?inE ?elems_fset0 ?elems_fset1; cbv delta) ||
    (rcondf ^if; first by auto=> />; cbv delta; rewrite ?inE ?elems_fset0 ?elems_fset1; cbv delta) ||
    (rcondt ^while; first by auto=> />; cbv delta; rewrite ?inE ?elems_fset0 ?elems_fset1; cbv delta) ||
    (rcondf ^while; first by auto=> />; cbv delta; rewrite ?inE ?elems_fset0 ?elems_fset1; cbv delta)).
  by auto=> />; cbv delta; rewrite ?inE ?elems_fset0 ?elems_fset1; cbv delta; rewrite ?inE; cbv delta.
qed.

(* The exact counter witness terminates with the asserted counters. *)
lemma beekem_actual_addition_counter_probability_one :
  phoare [BeeKemWitnessAdditionCounterGame.main_with_fixed_bit :
       users = [beekem_witness_user]
    /\ group = beekem_witness_group
    /\ kappa = 1
    /\ membership = beekem_witness_membership
    /\ hidden_bit = false
    ==>
       ! res.`bke_hidden_bit
    /\ ! res.`bke_adversary_guess
    /\ res.`bke_safe
    /\ ! res.`bke_protocol_consistency_failure
    /\ res.`bke_challenge_count = 0
    /\ res.`bke_member_addition_count = 1
    /\ res.`bke_win] = 1%r.
proof.
  proc; inline *.
  do ! (
    (rcondt ^if; first by auto=> />; cbv delta; rewrite ?inE ?elems_fset0 ?elems_fset1; cbv delta) ||
    (rcondf ^if; first by auto=> />; cbv delta; rewrite ?inE ?elems_fset0 ?elems_fset1; cbv delta) ||
    (rcondt ^while; first by auto=> />; cbv delta; rewrite ?inE ?elems_fset0 ?elems_fset1; cbv delta) ||
    (rcondf ^while; first by auto=> />; cbv delta; rewrite ?inE ?elems_fset0 ?elems_fset1; cbv delta)).
  by auto=> />; cbv delta; rewrite ?inE ?elems_fset0 ?elems_fset1; cbv delta; rewrite ?inE; cbv delta.
qed.
