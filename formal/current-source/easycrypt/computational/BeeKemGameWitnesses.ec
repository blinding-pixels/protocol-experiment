require import AllCore List FSet.
require import BeeKemTypes BeeKemQueryLog BeeKemProtocol BeeKemSafety BeeKemKiGame.

(* -------------------------------------------------------------------- *)
(* A deterministic, deliberately distinguishable protocol fixture.  It is not
   a claimed BeeKEM instantiation.  Its only purpose is to force the exact
   Figure 8 challenger to execute Create, SendUpdate, Challenge, both hidden-bit
   branches, the final adversary guess, and the public safety gate. *)

op beekem_witness_user : beekem_user = BeeKemUser 701.
op beekem_witness_group : beekem_group = BeeKemGroup 702.
op beekem_witness_create_id : beekem_operation_id = BeeKemOperationId 703.
op beekem_witness_update_id : beekem_operation_id = BeeKemOperationId 704.
op beekem_witness_add_id : beekem_operation_id = BeeKemOperationId 705.
op beekem_witness_remove_id : beekem_operation_id = BeeKemOperationId 706.
op beekem_witness_personal_id : beekem_operation_id = BeeKemOperationId 700.
op beekem_witness_real_secret : beekem_group_secret =
  BeeKemGroupSecret [true].
op beekem_witness_alternate_secret : beekem_group_secret =
  BeeKemGroupSecret [false].

op beekem_witness_tree : beekem_tree =
  {| bt_root = None;
     bt_nodes = [];
     bt_leaf_of = fun id => None |}.

op beekem_witness_personal_secret
    (owner : beekem_user) : beekem_personal_secret =
  {| bps_owner = owner;
     bps_generation = BeeKemGeneration 1;
     bps_public_key = BeeKemPublicKey 709;
     bps_secret_key = BeeKemSecretKey 710;
     bps_established_by = beekem_witness_personal_id |}.

op beekem_witness_initial_member_state
    (owner : beekem_user)
    (group : beekem_group) : beekem_member_state =
  {| bms_user = owner;
     bms_group = Some group;
     bms_operations = [];
     bms_frontier = fset0;
     bms_tree = beekem_witness_tree;
     bms_leaf = None;
     bms_current_personal_secret = beekem_witness_personal_secret owner;
     bms_retained_personal_secrets = [];
     bms_current_group_secret = None;
     bms_pending_structural_operations = false |}.

op beekem_witness_operation
    (id : beekem_operation_id)
    (author : beekem_user)
    (counter : int)
    (kind : beekem_operation_kind)
    (target : beekem_user option)
    (direct ancestry : beekem_operation_id fset) : beekem_operation =
  {| bo_id = id;
     bo_group = beekem_witness_group;
     bo_author = author;
     bo_author_counter = BeeKemCounter counter;
     bo_kind = kind;
     bo_target = target;
     bo_direct_predecessors = direct;
     bo_ancestry = ancestry;
     bo_leaf_public_key = None;
     bo_version_path = [];
     bo_control_payload = BeeKemControlPayload counter |}.

op beekem_witness_create_operation : beekem_operation =
  beekem_witness_operation
    beekem_witness_create_id beekem_witness_user 1 BeeCreate None fset0 fset0.

op beekem_witness_update_operation : beekem_operation =
  beekem_witness_operation
    beekem_witness_update_id beekem_witness_user 2 BeeUpdate None
    (fset1 beekem_witness_create_id) (fset1 beekem_witness_create_id).

op beekem_witness_add_operation (target : beekem_user) : beekem_operation =
  beekem_witness_operation
    beekem_witness_add_id beekem_witness_user 2 BeeAdd (Some target)
    (fset1 beekem_witness_create_id) (fset1 beekem_witness_create_id).

op beekem_witness_remove_operation (target : beekem_user) : beekem_operation =
  beekem_witness_operation
    beekem_witness_remove_id beekem_witness_user 2 BeeRemove (Some target)
    (fset1 beekem_witness_create_id) (fset1 beekem_witness_create_id).

op beekem_witness_control
    (operation : beekem_operation)
    (secret : beekem_secret_output)
    (needs_response : bool) : beekem_generated_message =
  {| bgm_operation = operation;
     bgm_direct_messages = [];
     bgm_sender_secret = secret;
     bgm_needs_response = needs_response |}.

op beekem_witness_after_create
    (state : beekem_member_state) : beekem_member_state =
  {| state with
     bms_operations = [beekem_witness_create_operation];
     bms_frontier = fset1 beekem_witness_create_id;
     bms_current_group_secret = None |}.

op beekem_witness_after_update
    (state : beekem_member_state) : beekem_member_state =
  {| state with
     bms_operations = rcons state.`bms_operations beekem_witness_update_operation;
     bms_frontier = fset1 beekem_witness_update_id;
     bms_current_group_secret = Some beekem_witness_real_secret |}.

op beekem_witness_after_add
    (state : beekem_member_state)
    (target : beekem_user) : beekem_member_state =
  {| state with
     bms_operations = rcons state.`bms_operations
       (beekem_witness_add_operation target);
     bms_frontier = fset1 beekem_witness_add_id;
     bms_current_group_secret = None |}.

op beekem_witness_after_remove
    (state : beekem_member_state)
    (target : beekem_user) : beekem_member_state =
  {| state with
     bms_operations = rcons state.`bms_operations
       (beekem_witness_remove_operation target);
     bms_frontier = fset1 beekem_witness_remove_id;
     bms_current_group_secret = None |}.

module BeeKemWitnessProtocol : BEEKEM_PROTOCOL_ALGORITHMS = {
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
      {| bpr_state = beekem_witness_after_add state target;
         bpr_control = Some
           (beekem_witness_control
             (beekem_witness_add_operation target) BeeSecretNoOutput false);
         bpr_secret = BeeSecretNoOutput |};
  }

  proc remove_member(
    state : beekem_member_state,
    target : beekem_user
  ) : beekem_protocol_result = {
    return
      {| bpr_state = beekem_witness_after_remove state target;
         bpr_control = Some
           (beekem_witness_control
             (beekem_witness_remove_operation target) BeeSecretNoOutput true);
         bpr_secret = BeeSecretNoOutput |};
  }

  proc update(
    state : beekem_member_state
  ) : beekem_protocol_result = {
    return
      {| bpr_state = beekem_witness_after_update state;
         bpr_control = Some
           (beekem_witness_control
             beekem_witness_update_operation
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

op beekem_witness_membership (operations : beekem_operation list) :
    beekem_user fset =
  if operations = [] then fset0 else fset1 beekem_witness_user.

module BeeKemWitnessDistinguisher(O : BEEKEM_KI_ORACLES) = {
  proc attack() : bool = {
    var created : bool;
    var updated : bool;
    var answer : beekem_secret_output;

    created <@ O.create_group(beekem_witness_user, fset0);
    updated <@ O.send_update(beekem_witness_user);
    answer <@ O.challenge(beekem_witness_user, BeeKemCounter 2);
    return created /\ updated /\
      answer = BeeSecretValue beekem_witness_real_secret;
  }
}.

module BeeKemWitnessWrongGuess(O : BEEKEM_KI_ORACLES) = {
  proc attack() : bool = {
    var created : bool;
    var updated : bool;
    var answer : beekem_secret_output;

    created <@ O.create_group(beekem_witness_user, fset0);
    updated <@ O.send_update(beekem_witness_user);
    answer <@ O.challenge(beekem_witness_user, BeeKemCounter 2);
    return false;
  }
}.

module BeeKemWitnessGame =
  BeeKemKiGame(
    BeeKemWitnessDistinguisher,
    BeeKemWitnessProtocol
  ).

module BeeKemWitnessWrongGuessGame =
  BeeKemKiGame(
    BeeKemWitnessWrongGuess,
    BeeKemWitnessProtocol
  ).

(* The fixed-bit entry points below are the exact game code path, minus only the
   random draw of the bit.  They make each branch independently checker
   reachable. *)
lemma beekem_witness_real_branch_reachable :
  hoare [BeeKemWitnessGame.main_with_fixed_bit :
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

lemma beekem_witness_random_branch_reachable :
  hoare [BeeKemWitnessGame.main_with_fixed_bit :
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

lemma beekem_witness_wrong_guess_changes_result :
  hoare [BeeKemWitnessWrongGuessGame.main_with_fixed_bit :
       users = [beekem_witness_user]
    /\ group = beekem_witness_group
    /\ kappa = 1
    /\ membership = beekem_witness_membership
    /\ hidden_bit = true
    ==>
       res.`bke_safe
    /\ res.`bke_challenge_count = 1
    /\ ! res.`bke_adversary_guess
    /\ ! res.`bke_win].
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

lemma beekem_witness_real_fixed_bit_wins_probability_one &m :
  Pr[
    BeeKemWitnessGame.main_with_fixed_bit(
      [beekem_witness_user],
      beekem_witness_group,
      1,
      beekem_witness_membership,
      true
    ) @ &m : res.`bke_win
  ] = 1%r.
proof.
  byphoare => //.
  conseq beekem_witness_real_branch_reachable => //.
qed.
