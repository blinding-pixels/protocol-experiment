require import AllCore List FSet.
require import BeeKemTypes BeeKemQueryLog BeeKemProtocol BeeKemSafety BeeKemKiGame.
require import BeeKemGameWitnesses LiveBeeKemAuthoritativeTypes.

(* Canonical-oracle forwarding seam for the application adapter.  This module
   deliberately owns no hidden bit, random sampler, safety predicate, query log,
   or protocol state.  Every call is forwarded to the authoritative Figure-8
   interface, so the BeeKemKiGame remains the sole owner of those objects.  The
   application identity, group, address, and three-way output representations
   are defined separately in [LiveBeeKemAuthoritativeTypes]. *)
module AuthoritativeBeeKemOracleForwarder(
  O : BEEKEM_KI_ORACLES
) = {
  proc create_group(
    creator : beekem_user,
    initial_members : beekem_user fset
  ) : bool = {
    var accepted : bool;
    accepted <@ O.create_group(creator, initial_members);
    return accepted;
  }

  proc add_member(
    actor : beekem_user,
    target : beekem_user
  ) : bool = {
    var accepted : bool;
    accepted <@ O.add_member(actor, target);
    return accepted;
  }

  proc remove_member(
    actor : beekem_user,
    target : beekem_user
  ) : bool = {
    var accepted : bool;
    accepted <@ O.remove_member(actor, target);
    return accepted;
  }

  proc send_update(actor : beekem_user) : bool = {
    var accepted : bool;
    accepted <@ O.send_update(actor);
    return accepted;
  }

  proc deliver(
    sender : beekem_user,
    counter : beekem_counter,
    recipient : beekem_user
  ) : bool = {
    var accepted : bool;
    accepted <@ O.deliver(sender, counter, recipient);
    return accepted;
  }

  proc reveal(
    sender : beekem_user,
    counter : beekem_counter
  ) : beekem_secret_output = {
    var answer : beekem_secret_output;
    answer <@ O.reveal(sender, counter);
    return answer;
  }

  proc challenge(
    sender : beekem_user,
    counter : beekem_counter
  ) : beekem_secret_output = {
    var answer : beekem_secret_output;
    answer <@ O.challenge(sender, counter);
    return answer;
  }

  proc compromise(id : beekem_user) : beekem_member_state option = {
    var answer : beekem_member_state option;
    answer <@ O.compromise(id);
    return answer;
  }

  proc get_control_message(
    sender : beekem_user,
    counter : beekem_counter
  ) : beekem_generated_message option = {
    var answer : beekem_generated_message option;
    answer <@ O.get_control_message(sender, counter);
    return answer;
  }

  proc get_direct_message(
    sender : beekem_user,
    counter : beekem_counter,
    recipient : beekem_user
  ) : beekem_direct_message option = {
    var answer : beekem_direct_message option;
    answer <@ O.get_direct_message(sender, counter, recipient);
    return answer;
  }
}.

(* This adversary reaches a canonical Create -> Update -> Challenge trace only
   through the forwarding seam.  In particular, [challenge] still invokes the
   authoritative game oracle, so accepted challenge counting, same-length
   random sampling, and the final safety gate remain challenger-owned. *)
module AuthoritativeForwarderWitness(
  O : BEEKEM_KI_ORACLES
) = {
  module F = AuthoritativeBeeKemOracleForwarder(O)

  proc attack() : bool = {
    var created : bool;
    var updated : bool;
    var answer : beekem_secret_output;

    created <@ F.create_group(beekem_witness_user, fset0);
    updated <@ F.send_update(beekem_witness_user);
    answer <@ F.challenge(beekem_witness_user, BeeKemCounter 2);
    return created /\ updated /\
      answer = BeeSecretValue beekem_witness_real_secret;
  }
}.

module AuthoritativeForwarderWitnessGame =
  BeeKemKiGame(
    AuthoritativeForwarderWitness,
    BeeKemWitnessProtocol
  ).

lemma authoritative_forwarder_real_branch_reachable :
  hoare [AuthoritativeForwarderWitnessGame.main_with_fixed_bit :
       users = [beekem_witness_user]
    /\ group = beekem_witness_group
    /\ kappa = 1
    /\ membership = beekem_witness_membership
    /\ hidden_bit = true
    ==>
       res.`bke_hidden_bit
    /\ res.`bke_adversary_guess
    /\ res.`bke_safe
    /\ ! res.`bke_protocol_consistency_failure
    /\ res.`bke_challenge_count = 1
    /\ res.`bke_member_addition_count = 0
    /\ res.`bke_real_branch_count = 1
    /\ res.`bke_random_branch_count = 0
    /\ res.`bke_random_sample_count = 0
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
    /beekem_witness_after_create /beekem_witness_after_update
    /beekem_witness_control /beekem_witness_create_operation
    /beekem_witness_update_operation /beekem_witness_operation
    /beekem_control_operation_id /beekem_control_operation
    /beekem_counter_value /beekem_empty_protocol_state
    /beekem_secret_output_is_undefined /beekem_secret_output_is_value
    /beekem_secret_output_value /beekem_operation_precedes_or_equals
    /beekem_operation_precedes /bee_safe_kappa /beekem_all_challenges_safe
    /beekem_challenge_safe_against /beekem_query_successful
    /beekem_query_is_challenge /beekem_query_is_compromise.
  smt(in_fset0 in_fset1 size_rcons size_ge0).
qed.

lemma authoritative_forwarder_random_branch_reachable :
  hoare [AuthoritativeForwarderWitnessGame.main_with_fixed_bit :
       users = [beekem_witness_user]
    /\ group = beekem_witness_group
    /\ kappa = 1
    /\ membership = beekem_witness_membership
    /\ hidden_bit = false
    ==>
       ! res.`bke_hidden_bit
    /\ res.`bke_safe
    /\ ! res.`bke_protocol_consistency_failure
    /\ res.`bke_challenge_count = 1
    /\ res.`bke_member_addition_count = 0
    /\ res.`bke_real_branch_count = 0
    /\ res.`bke_random_branch_count = 1
    /\ res.`bke_random_sample_count = 1].
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
    /beekem_query_is_challenge /beekem_query_is_compromise.
  smt(in_fset0 in_fset1 size_rcons size_ge0).
qed.
