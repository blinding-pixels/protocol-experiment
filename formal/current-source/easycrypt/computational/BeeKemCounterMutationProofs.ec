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
    /beekem_witness_after_create /beekem_witness_after_update
    /beekem_witness_control /beekem_witness_create_operation
    /beekem_witness_update_operation /beekem_witness_operation
    /beekem_control_operation_id /beekem_control_operation
    /beekem_counter_value /beekem_empty_protocol_state
    /beekem_secret_output_is_undefined /beekem_secret_output_is_value
    /beekem_secret_output_value /beekem_operation_precedes_or_equals
    /beekem_operation_precedes /bee_safe_kappa /beekem_all_challenges_safe
    /beekem_challenge_safe_against /beekem_query_successful
    /beekem_query_is_challenge /beekem_query_is_compromise
    /beekem_counter_initial_members /beekem_counter_first_target
    /beekem_counter_second_target /beekem_drop_one_count
    /beekem_is_ceil_log2 /beekem_theorem1_loss.
  rewrite -cardE fcardU1 fcard1 in_fset1.
  smt(in_fset0 in_fset1 size_rcons size_ge0).
qed.
