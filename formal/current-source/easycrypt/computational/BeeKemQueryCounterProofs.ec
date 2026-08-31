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
  proc.
  inline *.
  rcondt ^while; first by auto.
  rcondf ^while; first by auto.
  rcondf ^while; first by auto.
  rcondt ^while; first by auto.
  rcondf ^while; first by auto.
  rcondf ^while; first by auto.
  auto.
  rewrite /beekem_witness_membership /beekem_witness_initial_member_state
    /beekem_member_retention_valid /beekem_witness_personal_secret
    /beekem_witness_after_create /beekem_witness_after_add
    /beekem_witness_control /beekem_witness_create_operation
    /beekem_witness_add_operation /beekem_witness_operation
    /beekem_control_operation_id /beekem_control_operation
    /beekem_counter_value /beekem_empty_protocol_state
    /beekem_secret_output_is_undefined /beekem_secret_output_is_value
    /beekem_secret_output_value /beekem_operation_precedes_or_equals
    /beekem_operation_precedes /bee_safe_kappa /beekem_all_challenges_safe
    /beekem_challenge_safe_against /beekem_query_successful
    /beekem_query_is_challenge /beekem_query_is_compromise
    /beekem_witness_add_target.
  smt(in_fset0 in_fset1 size_rcons size_ge0).
qed.
