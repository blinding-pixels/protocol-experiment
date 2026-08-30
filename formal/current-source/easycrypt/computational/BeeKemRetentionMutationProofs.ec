require import AllCore List FSet.
require import BeeKemTypes BeeKemQueryLog BeeKemProtocol BeeKemSafety BeeKemKiGame.
require import BeeKemGameWitnesses.

(* Finite-kappa retention is part of the executable protocol state, not merely
   a side assumption on the imported theorem.  The snapshot exposure below is
   exactly the current personal secret plus the retained older suffix returned
   by CompromiseProtocolState. *)
op beekem_personal_secret_exposure
    (state : beekem_member_state) : beekem_personal_secret list =
  state.`bms_current_personal_secret ::
    state.`bms_retained_personal_secrets.

op beekem_retention_second_update_id : beekem_operation_id =
  BeeKemOperationId 740.
op beekem_retention_first_personal_id : beekem_operation_id =
  BeeKemOperationId 741.
op beekem_retention_second_personal_id : beekem_operation_id =
  BeeKemOperationId 742.

op beekem_retention_personal_secret
    (owner : beekem_user)
    (generation : int)
    (established_by : beekem_operation_id) : beekem_personal_secret =
  {| bps_owner = owner;
     bps_generation = BeeKemGeneration generation;
     bps_public_key = BeeKemPublicKey (750 + generation);
     bps_secret_key = BeeKemSecretKey (760 + generation);
     bps_established_by = established_by |}.

op beekem_retention_first_personal_secret
    (owner : beekem_user) : beekem_personal_secret =
  beekem_retention_personal_secret
    owner 2 beekem_retention_first_personal_id.

op beekem_retention_second_personal_secret
    (owner : beekem_user) : beekem_personal_secret =
  beekem_retention_personal_secret
    owner 3 beekem_retention_second_personal_id.

op beekem_retention_second_update_operation : beekem_operation =
  beekem_witness_operation
    beekem_retention_second_update_id
    beekem_witness_user
    3
    BeeUpdate
    None
    (fset1 beekem_witness_update_id)
    (fset1 beekem_witness_create_id `|` fset1 beekem_witness_update_id).

op beekem_retention_after_update
    (state : beekem_member_state)
    (operation : beekem_operation)
    (personal : beekem_personal_secret)
    (retain_old : bool) : beekem_member_state =
  {| state with
     bms_operations = rcons state.`bms_operations operation;
     bms_frontier = fset1 operation.`bo_id;
     bms_current_personal_secret = personal;
     bms_retained_personal_secrets =
       if retain_old
       then state.`bms_current_personal_secret ::
              state.`bms_retained_personal_secrets
       else [];
     bms_current_group_secret = Some beekem_witness_real_secret |}.

op beekem_retention_exact_final_state : beekem_member_state =
  beekem_retention_after_update
    (beekem_retention_after_update
       (beekem_witness_after_create
          (beekem_witness_initial_member_state
             beekem_witness_user beekem_witness_group))
       beekem_witness_update_operation
       (beekem_retention_first_personal_secret beekem_witness_user)
       false)
    beekem_retention_second_update_operation
    (beekem_retention_second_personal_secret beekem_witness_user)
    false.

op beekem_retention_disabled_final_state : beekem_member_state =
  beekem_retention_after_update
    (beekem_retention_after_update
       (beekem_witness_after_create
          (beekem_witness_initial_member_state
             beekem_witness_user beekem_witness_group))
       beekem_witness_update_operation
       (beekem_retention_first_personal_secret beekem_witness_user)
       true)
    beekem_retention_second_update_operation
    (beekem_retention_second_personal_secret beekem_witness_user)
    true.

lemma finite_retention_exposes_only_current_personal_secret :
  beekem_personal_secret_exposure beekem_retention_exact_final_state =
    [beekem_retention_second_personal_secret beekem_witness_user]
  /\ beekem_member_retention_valid 1 beekem_retention_exact_final_state.
proof.
  by rewrite /beekem_personal_secret_exposure
    /beekem_retention_exact_final_state /beekem_retention_after_update
    /beekem_member_retention_valid.
qed.

lemma disabled_retention_expands_compromise_exposure :
  beekem_personal_secret_exposure beekem_retention_disabled_final_state =
    [beekem_retention_second_personal_secret beekem_witness_user;
     beekem_retention_first_personal_secret beekem_witness_user;
     beekem_witness_personal_secret beekem_witness_user]
  /\ ! beekem_member_retention_valid 1 beekem_retention_disabled_final_state.
proof.
  by rewrite /beekem_personal_secret_exposure
    /beekem_retention_disabled_final_state /beekem_retention_after_update
    /beekem_witness_after_create /beekem_witness_initial_member_state
    /beekem_member_retention_valid.
qed.

module BeeKemExactRetentionProtocol : BEEKEM_PROTOCOL_ALGORITHMS = {
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
    var first_update : bool;
    var next_operation : beekem_operation;
    var next_personal : beekem_personal_secret;
    var next_state : beekem_member_state;

    first_update <- size state.`bms_operations = 1;
    next_operation <-
      if first_update
      then beekem_witness_update_operation
      else beekem_retention_second_update_operation;
    next_personal <-
      if first_update
      then beekem_retention_first_personal_secret state.`bms_user
      else beekem_retention_second_personal_secret state.`bms_user;
    next_state <- beekem_retention_after_update
      state next_operation next_personal false;

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

(* Single mutation: the protocol keeps every previous personal secret rather
   than truncating the suffix to the kappa-most-recent window.  All control
   operations, counters, group-secret outputs, and adversary scheduling remain
   byte-for-byte the same as the exact fixture. *)
module BeeKemDisabledRetentionProtocol : BEEKEM_PROTOCOL_ALGORITHMS = {
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
    var first_update : bool;
    var next_operation : beekem_operation;
    var next_personal : beekem_personal_secret;
    var next_state : beekem_member_state;

    first_update <- size state.`bms_operations = 1;
    next_operation <-
      if first_update
      then beekem_witness_update_operation
      else beekem_retention_second_update_operation;
    next_personal <-
      if first_update
      then beekem_retention_first_personal_secret state.`bms_user
      else beekem_retention_second_personal_secret state.`bms_user;
    next_state <- beekem_retention_after_update
      state next_operation next_personal true;

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

module BeeKemRetentionExposureAdversary(O : BEEKEM_KI_ORACLES) = {
  proc attack() : bool = {
    var created : bool;
    var first_updated : bool;
    var challenged : beekem_secret_output;
    var second_updated : bool;
    var compromised : beekem_member_state option;
    var exposed : beekem_personal_secret list;

    exposed <- [];
    created <@ O.create_group(beekem_witness_user, fset0);
    first_updated <@ O.send_update(beekem_witness_user);
    challenged <@ O.challenge(beekem_witness_user, BeeKemCounter 2);
    second_updated <@ O.send_update(beekem_witness_user);
    compromised <@ O.compromise(beekem_witness_user);
    if (compromised <> None) {
      exposed <- beekem_personal_secret_exposure (oget compromised);
    }

    return created /\ first_updated /\ second_updated /\
      compromised <> None /\
      challenged = BeeSecretValue beekem_witness_real_secret /\
      1 < size exposed;
  }
}.

module BeeKemExactRetentionGame =
  BeeKemKiGame(
    BeeKemRetentionExposureAdversary,
    BeeKemExactRetentionProtocol
  ).

module BeeKemDisabledRetentionGame =
  BeeKemKiGame(
    BeeKemRetentionExposureAdversary,
    BeeKemDisabledRetentionProtocol
  ).

lemma finite_retention_blocks_extra_snapshot_exposure_in_actual_ki_game :
  hoare [BeeKemExactRetentionGame.main_with_fixed_bit :
       users = [beekem_witness_user]
    /\ group = beekem_witness_group
    /\ kappa = 1
    /\ membership = beekem_witness_membership
    /\ hidden_bit = true
    ==>
       res.`bke_hidden_bit
    /\ ! res.`bke_adversary_guess
    /\ res.`bke_safe
    /\ ! res.`bke_protocol_consistency_failure
    /\ res.`bke_challenge_count = 1
    /\ res.`bke_member_addition_count = 0
    /\ res.`bke_real_branch_count = 1
    /\ res.`bke_random_branch_count = 0
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
  rcondt ^while; first by auto.
  rcondf ^while; first by auto.
  rcondf ^while; first by auto.
  auto.
  rewrite /beekem_witness_membership /beekem_witness_initial_member_state
    /beekem_witness_personal_secret /beekem_member_retention_valid
    /beekem_witness_after_create /beekem_retention_after_update
    /beekem_retention_first_personal_secret
    /beekem_retention_second_personal_secret
    /beekem_retention_personal_secret /beekem_personal_secret_exposure
    /beekem_witness_control /beekem_witness_create_operation
    /beekem_witness_update_operation /beekem_retention_second_update_operation
    /beekem_witness_operation /beekem_control_operation_id
    /beekem_control_operation /beekem_counter_value
    /beekem_empty_protocol_state /beekem_secret_output_is_undefined
    /beekem_secret_output_is_value /beekem_secret_output_value
    /beekem_operation_precedes_or_equals /beekem_operation_precedes
    /bee_safe_kappa /beekem_all_challenges_safe
    /beekem_challenge_safe_against /beekem_challenge_compromise_pair_safe
    /beekem_kappa_fsu_clause /beekem_pcs_clause /beekem_kappa_cfs_clause
    /beekem_update_chain_between /beekem_update_chain_ending_at
    /beekem_successful_update_for /beekem_q2op_precedes
    /beekem_q2op_precedes_or_equals /beekem_q2op_concurrent
    /beekem_q2op_set /beekem_ids_precede_frontier
    /beekem_ids_precede_or_equal_frontier /beekem_id_precedes_some
    /beekem_id_precedes_or_equals_some /beekem_ids_pairwise_concurrent
    /beekem_id_concurrent_with_all /beekem_operation_ids_concurrent
    /beekem_operation_id_precedes /beekem_operation_id_precedes_or_equals
    /beekem_operation_id_known /beekem_query_successful
    /beekem_query_is_send_update /beekem_query_is_challenge
    /beekem_query_is_compromise /beekem_ki_final_win.
  rewrite (elems_fset1 beekem_witness_create_id)
    (elems_fset1 beekem_witness_update_id)
    (elems_fset1 beekem_retention_second_update_id).
  smt(in_fset0 in_fset1 in_fsetU size_rcons size_ge0).
qed.

lemma disabling_finite_retention_reaches_actual_ki_game :
  hoare [BeeKemDisabledRetentionGame.main_with_fixed_bit :
       users = [beekem_witness_user]
    /\ group = beekem_witness_group
    /\ kappa = 1
    /\ membership = beekem_witness_membership
    /\ hidden_bit = true
    ==>
       res.`bke_hidden_bit
    /\ res.`bke_adversary_guess
    /\ res.`bke_safe
    /\ res.`bke_protocol_consistency_failure
    /\ res.`bke_challenge_count = 1
    /\ res.`bke_member_addition_count = 0
    /\ res.`bke_real_branch_count = 1
    /\ res.`bke_random_branch_count = 0
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
  rcondt ^while; first by auto.
  rcondf ^while; first by auto.
  rcondf ^while; first by auto.
  auto.
  rewrite /beekem_witness_membership /beekem_witness_initial_member_state
    /beekem_witness_personal_secret /beekem_member_retention_valid
    /beekem_witness_after_create /beekem_retention_after_update
    /beekem_retention_first_personal_secret
    /beekem_retention_second_personal_secret
    /beekem_retention_personal_secret /beekem_personal_secret_exposure
    /beekem_witness_control /beekem_witness_create_operation
    /beekem_witness_update_operation /beekem_retention_second_update_operation
    /beekem_witness_operation /beekem_control_operation_id
    /beekem_control_operation /beekem_counter_value
    /beekem_empty_protocol_state /beekem_secret_output_is_undefined
    /beekem_secret_output_is_value /beekem_secret_output_value
    /beekem_operation_precedes_or_equals /beekem_operation_precedes
    /bee_safe_kappa /beekem_all_challenges_safe
    /beekem_challenge_safe_against /beekem_challenge_compromise_pair_safe
    /beekem_kappa_fsu_clause /beekem_pcs_clause /beekem_kappa_cfs_clause
    /beekem_update_chain_between /beekem_update_chain_ending_at
    /beekem_successful_update_for /beekem_q2op_precedes
    /beekem_q2op_precedes_or_equals /beekem_q2op_concurrent
    /beekem_q2op_set /beekem_ids_precede_frontier
    /beekem_ids_precede_or_equal_frontier /beekem_id_precedes_some
    /beekem_id_precedes_or_equals_some /beekem_ids_pairwise_concurrent
    /beekem_id_concurrent_with_all /beekem_operation_ids_concurrent
    /beekem_operation_id_precedes /beekem_operation_id_precedes_or_equals
    /beekem_operation_id_known /beekem_query_successful
    /beekem_query_is_send_update /beekem_query_is_challenge
    /beekem_query_is_compromise /beekem_ki_final_win.
  rewrite (elems_fset1 beekem_witness_create_id)
    (elems_fset1 beekem_witness_update_id)
    (elems_fset1 beekem_retention_second_update_id).
  smt(in_fset0 in_fset1 in_fsetU size_rcons size_ge0).
qed.
