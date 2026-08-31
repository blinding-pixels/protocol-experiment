require import AllCore List FSet.
require import BeeKemTypes BeeKemQueryLog BeeKemProtocol BeeKemSafety BeeKemKiGame.
require import BeeKemGameWitnesses.

(* A deterministic negative-control protocol used only to drive the exact KI
   game through two fork-sensitive traces.  The first update is the challenge
   node.  A second update is a concurrent sibling.  Alternatively, a
   secret-bearing Add is causally after the first update.  This module is not a
   claimed BeeKEM instantiation and is never used by the imported theorem. *)
op beekem_fork_second_update_id : beekem_operation_id =
  BeeKemOperationId 730.
op beekem_fork_causal_add_id : beekem_operation_id =
  BeeKemOperationId 731.
op beekem_fork_add_target : beekem_user = BeeKemUser 732.

op beekem_fork_second_update_operation : beekem_operation =
  beekem_witness_operation
    beekem_fork_second_update_id beekem_witness_user 3 BeeUpdate None
    (fset1 beekem_witness_create_id)
    (fset1 beekem_witness_create_id).

op beekem_fork_causal_add_operation
    (target : beekem_user) : beekem_operation =
  beekem_witness_operation
    beekem_fork_causal_add_id beekem_witness_user 3 BeeAdd (Some target)
    (fset1 beekem_witness_update_id)
    (fset1 beekem_witness_create_id `|` fset1 beekem_witness_update_id).

op beekem_fork_after_second_update
    (state : beekem_member_state) : beekem_member_state =
  {| state with
     bms_operations =
       rcons state.`bms_operations beekem_fork_second_update_operation;
     bms_frontier = fset1 beekem_fork_second_update_id;
     bms_current_group_secret = Some beekem_witness_real_secret |}.

op beekem_fork_after_causal_add
    (state : beekem_member_state)
    (target : beekem_user) : beekem_member_state =
  {| state with
     bms_operations =
       rcons state.`bms_operations (beekem_fork_causal_add_operation target);
     bms_frontier = fset1 beekem_fork_causal_add_id;
     bms_current_group_secret = Some beekem_witness_real_secret |}.

module BeeKemForkWitnessProtocol : BEEKEM_PROTOCOL_ALGORITHMS = {
  proc init(
    id : beekem_user,
    group : beekem_group,
    kappa : int
  ) : beekem_member_state = {
    return beekem_witness_initial_member_state id group;
  }

  proc create(
    state : beekem_member_state,
    initial_members : beekem_user fset
  ) : beekem_protocol_result = {
    return
      {| bpr_state = beekem_witness_after_create state;
         bpr_control = Some
           (beekem_witness_control
             beekem_witness_create_operation BeeSecretNoOutput true);
         bpr_secret = BeeSecretNoOutput |};
  }

  proc add(
    state : beekem_member_state,
    target : beekem_user
  ) : beekem_protocol_result = {
    return
      {| bpr_state = beekem_fork_after_causal_add state target;
         bpr_control = Some
           (beekem_witness_control
             (beekem_fork_causal_add_operation target)
             (BeeSecretValue beekem_witness_real_secret)
             false);
         bpr_secret = BeeSecretValue beekem_witness_real_secret |};
  }

  proc remove_member(
    state : beekem_member_state,
    target : beekem_user
  ) : beekem_protocol_result = {
    return
      {| bpr_state = beekem_witness_after_remove state target;
         bpr_control = Some
           (beekem_witness_control
             (beekem_witness_remove_operation target)
             BeeSecretNoOutput
             true);
         bpr_secret = BeeSecretNoOutput |};
  }

  proc update(
    state : beekem_member_state
  ) : beekem_protocol_result = {
    var first_update : bool;
    var next_state : beekem_member_state;
    var next_operation : beekem_operation;

    first_update <- size state.`bms_operations = 1;
    next_state <-
      if first_update
      then beekem_witness_after_update state
      else beekem_fork_after_second_update state;
    next_operation <-
      if first_update
      then beekem_witness_update_operation
      else beekem_fork_second_update_operation;

    return
      {| bpr_state = next_state;
         bpr_control = Some
           (beekem_witness_control
             next_operation
             (BeeSecretValue beekem_witness_real_secret)
             true);
         bpr_secret = BeeSecretValue beekem_witness_real_secret |};
  }

  proc process(
    state : beekem_member_state,
    sender : beekem_user,
    control : beekem_generated_message,
    direct : beekem_direct_message option
  ) : beekem_process_result = {
    return
      {| bxr_state = state;
         bxr_control = None;
         bxr_sender_secret = control.`bgm_sender_secret;
         bxr_response_secret = BeeSecretNoOutput |};
  }
}.

module BeeKemCfsForkExposureAdversary(O : BEEKEM_KI_ORACLES) = {
  proc attack() : bool = {
    var created : bool;
    var first_updated : bool;
    var second_updated : bool;
    var answer : beekem_secret_output;
    var compromised : beekem_member_state option;

    created <@ O.create_group(beekem_witness_user, fset0);
    first_updated <@ O.send_update(beekem_witness_user);
    answer <@ O.challenge(beekem_witness_user, BeeKemCounter 2);
    second_updated <@ O.send_update(beekem_witness_user);
    compromised <@ O.compromise(beekem_witness_user);

    return created /\ first_updated /\ second_updated /\
      compromised <> None /\
      answer = BeeSecretValue beekem_witness_real_secret;
  }
}.

module BeeKemCausalAncestryExposureAdversary(O : BEEKEM_KI_ORACLES) = {
  proc attack() : bool = {
    var created : bool;
    var updated : bool;
    var added : bool;
    var compromised : beekem_member_state option;
    var answer : beekem_secret_output;

    created <@ O.create_group(beekem_witness_user, fset0);
    updated <@ O.send_update(beekem_witness_user);
    compromised <@ O.compromise(beekem_witness_user);
    added <@ O.add_member(beekem_witness_user, beekem_fork_add_target);
    answer <@ O.challenge(beekem_witness_user, BeeKemCounter 3);

    return created /\ updated /\ added /\ compromised <> None /\
      answer = BeeSecretValue beekem_witness_real_secret;
  }
}.
