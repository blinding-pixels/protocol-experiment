require import AllCore List FSet.
require import BeeKemTypes BeeKemQueryLog.

(* The algorithms are abstract cryptographic implementations, but their exact
   callable surface is the BeeKEM/DCGKA surface used by Figure 8.  In
   particular, Add and Remove are kept distinct, and Process returns separate
   sender and response secrets. *)
module type BEEKEM_PROTOCOL_ALGORITHMS = {
  proc init(
    id : beekem_user,
    group : beekem_group,
    kappa : int
  ) : beekem_member_state

  proc create(
    state : beekem_member_state,
    initial_members : beekem_user fset
  ) : beekem_protocol_result

  proc add(
    state : beekem_member_state,
    target : beekem_user
  ) : beekem_protocol_result

  proc remove_member(
    state : beekem_member_state,
    target : beekem_user
  ) : beekem_protocol_result

  proc update(
    state : beekem_member_state
  ) : beekem_protocol_result

  proc process(
    state : beekem_member_state,
    sender : beekem_user,
    control : beekem_generated_message,
    direct : beekem_direct_message option
  ) : beekem_process_result
}.

(* Figure 9 treats decentralized group membership as a deterministic function
   of the delivered control-message DAG.  It is a pure game parameter, exactly
   as in the paper's notation Pi[DGM], rather than an adversary supplied
   membership or admissibility bit. *)
type beekem_dgm = beekem_operation list -> beekem_user fset.

op beekem_control_operation
  (control : beekem_generated_message option) : beekem_operation option =
  if control = None
  then None
  else Some (oget control).`bgm_operation.

op beekem_control_operation_id
  (control : beekem_generated_message option) : beekem_operation_id option =
  if control = None
  then None
  else Some (oget control).`bgm_operation.`bo_id.

op beekem_counter_value (counter : int) : beekem_counter =
  BeeKemCounter counter.

module BeeKemOracleEnvironment(
  P : BEEKEM_PROTOCOL_ALGORITHMS
) = {
  var state : beekem_protocol_state
  var query_log : beekem_query_log
  var dgm : beekem_dgm

  (* This is Figure 8's explicit [win <- 1] protocol-correctness event.  It is
     not a safety or authentication switch and cannot make a query admissible. *)
  var protocol_consistency_failure : bool

  proc frontier(id : beekem_user) : beekem_operation_id fset = {
    var member_state : beekem_member_state option;
    var answer : beekem_operation_id fset;

    member_state <- state.`bps_member_states id;
    answer <- fset0;
    if (member_state <> None) {
      answer <- (oget member_state).`bms_frontier;
    }
    return answer;
  }

  proc record_query(
    kind : beekem_query_kind,
    actor : beekem_user,
    target : beekem_user option,
    counter : beekem_counter option,
    operation : beekem_operation_id option,
    actor_frontier : beekem_operation_id fset,
    target_frontier : beekem_operation_id fset,
    accepted : bool,
    rejection : beekem_query_rejection option
  ) : unit = {
    var query : beekem_query;

    query <-
      {| bq_id = BeeKemQueryId (size query_log + 1);
         bq_kind = kind;
         bq_actor = actor;
         bq_target = target;
         bq_counter = counter;
         bq_operation = operation;
         bq_actor_frontier = actor_frontier;
         bq_target_frontier = target_frontier;
         bq_accepted = accepted;
         bq_rejection = rejection |};
    query_log <- rcons query_log query;
  }

  proc initialize(
    users : beekem_user list,
    group : beekem_group,
    kappa : int,
    membership : beekem_dgm
  ) : unit = {
    var remaining : beekem_user list;
    var id : beekem_user;
    var initialized : beekem_member_state;

    state <- beekem_empty_protocol_state group kappa;
    query_log <- [];
    dgm <- membership;
    protocol_consistency_failure <- false;
    remaining <- users;

    while (remaining <> []) {
      id <- head witness remaining;
      remaining <- behead remaining;
      initialized <@ P.init(id, group, kappa);
      if (! beekem_member_retention_valid kappa initialized) {
        protocol_consistency_failure <- true;
      }
      state <-
        {| state with
           bps_initialized_users =
             state.`bps_initialized_users `|` fset1 id;
           bps_member_states =
             beekem_member_state_map_set
               state.`bps_member_states id (Some initialized) |};
    }
  }

  proc install_control(
    sender : beekem_user,
    counter : beekem_counter,
    control : beekem_generated_message,
    secret : beekem_secret_output,
    needs_response : bool,
    add_target : beekem_user option
  ) : unit = {
    var key : beekem_message_key;
    var operation : beekem_operation;
    var direct_messages : beekem_direct_message list;
    var direct : beekem_direct_message;
    var members : beekem_user fset;

    key <- (sender, counter);
    operation <- control.`bgm_operation;

    if (operation.`bo_author <> sender \/
        operation.`bo_author_counter <> counter \/
        control.`bgm_sender_secret <> secret) {
      protocol_consistency_failure <- true;
    }

    state <-
      {| state with
         bps_messages =
           beekem_message_map_set state.`bps_messages key (Some control);
         bps_secrets =
           beekem_secret_map_set state.`bps_secrets key secret;
         bps_add_targets =
           beekem_add_target_map_set state.`bps_add_targets key add_target;
         bps_needs_responses =
           beekem_needs_response_map_set
             state.`bps_needs_responses key needs_response;
         bps_delivery_marks =
           beekem_delivery_mark_map_set state.`bps_delivery_marks
             (sender, counter, sender) true;
         bps_operations = rcons state.`bps_operations operation |};

    direct_messages <- control.`bgm_direct_messages;
    while (direct_messages <> []) {
      direct <- head witness direct_messages;
      direct_messages <- behead direct_messages;
      if (direct.`bdm_sender <> sender \/
          direct.`bdm_operation <> operation.`bo_id) {
        protocol_consistency_failure <- true;
      }
      state <-
        {| state with
           bps_direct_messages =
             beekem_direct_message_map_set
               state.`bps_direct_messages
               (sender, counter, direct.`bdm_recipient)
               (Some direct) |};
    }

    members <- dgm state.`bps_operations;
    state <- {| state with bps_members = members |};
  }

  proc valid_member(id : beekem_user) : bool = {
    var remaining : beekem_operation list;
    var operation : beekem_operation;
    var answer : bool;

    remaining <- state.`bps_operations;
    answer <- false;
    while (remaining <> [] /\ ! answer) {
      operation <- head witness remaining;
      remaining <- behead remaining;
      if (state.`bps_delivery_marks
            (operation.`bo_author, operation.`bo_author_counter, id)) {
        answer <- true;
      }
    }
    return answer;
  }

  proc in_history_operation(
    operation : beekem_operation,
    recipient : beekem_user
  ) : bool = {
    var remaining : beekem_operation list;
    var later : beekem_operation;
    var answer : bool;

    remaining <- state.`bps_operations;
    answer <- false;
    while (remaining <> [] /\ ! answer) {
      later <- head witness remaining;
      remaining <- behead remaining;
      if (beekem_operation_precedes_or_equals operation later /\
          state.`bps_delivery_marks
            (later.`bo_author, later.`bo_author_counter, recipient)) {
        answer <- true;
      }
    }
    return answer;
  }

  proc in_history(
    sender : beekem_user,
    counter : beekem_counter,
    recipient : beekem_user
  ) : bool = {
    var control : beekem_generated_message option;
    var answer : bool;

    control <- state.`bps_messages (sender, counter);
    answer <- false;
    if (control <> None) {
      answer <@ in_history_operation(
        (oget control).`bgm_operation,
        recipient
      );
    }
    return answer;
  }

  proc operations_up_to(
    operation : beekem_operation
  ) : beekem_operation list = {
    var remaining : beekem_operation list;
    var candidate : beekem_operation;
    var selected : beekem_operation list;

    remaining <- state.`bps_operations;
    selected <- [];
    while (remaining <> []) {
      candidate <- head witness remaining;
      remaining <- behead remaining;
      if (beekem_operation_precedes_or_equals candidate operation) {
        selected <- rcons selected candidate;
      }
    }
    return selected;
  }

  proc operations_in_history(
    recipient : beekem_user
  ) : beekem_operation list = {
    var remaining : beekem_operation list;
    var candidate : beekem_operation;
    var selected : beekem_operation list;
    var contained : bool;

    remaining <- state.`bps_operations;
    selected <- [];
    while (remaining <> []) {
      candidate <- head witness remaining;
      remaining <- behead remaining;
      contained <@ in_history_operation(candidate, recipient);
      if (contained) {
        selected <- rcons selected candidate;
      }
    }
    return selected;
  }

  proc should_decrypt_operation(
    operation : beekem_operation,
    recipient : beekem_user
  ) : bool = {
    var controls : beekem_operation list;
    var members : beekem_user fset;

    controls <@ operations_up_to(operation);
    members <- dgm controls;
    return recipient \in members;
  }

  proc should_decrypt(
    sender : beekem_user,
    counter : beekem_counter,
    recipient : beekem_user
  ) : bool = {
    var control : beekem_generated_message option;
    var answer : bool;

    control <- state.`bps_messages (sender, counter);
    answer <- false;
    if (control <> None) {
      answer <@ should_decrypt_operation(
        (oget control).`bgm_operation,
        recipient
      );
    }
    return answer;
  }

  proc should_receive(
    sender : beekem_user,
    counter : beekem_counter,
    recipient : beekem_user
  ) : bool = {
    var control : beekem_generated_message option;
    var target : beekem_operation;
    var remaining : beekem_operation list;
    var candidate : beekem_operation;
    var selected : beekem_operation list;
    var contained : bool;
    var members : beekem_user fset;
    var answer : bool;

    control <- state.`bps_messages (sender, counter);
    selected <- [];
    members <- fset0;
    answer <- false;
    if (control <> None) {
      target <- (oget control).`bgm_operation;
      remaining <- state.`bps_operations;
      while (remaining <> []) {
        candidate <- head witness remaining;
        remaining <- behead remaining;
        contained <- false;
        if (beekem_operation_precedes_or_equals candidate target) {
          contained <- true;
        } else {
          contained <@ in_history_operation(candidate, recipient);
        }
        if (contained) {
          selected <- rcons selected candidate;
        }
      }
      members <- dgm selected;
      answer <- recipient \in members;
    }
    return answer;
  }

  proc causally_ready(
    sender : beekem_user,
    counter : beekem_counter,
    recipient : beekem_user
  ) : bool = {
    var control : beekem_generated_message option;
    var target : beekem_operation;
    var remaining : beekem_operation list;
    var candidate : beekem_operation;
    var contained : bool;
    var answer : bool;

    control <- state.`bps_messages (sender, counter);
    answer <- false;
    if (control <> None) {
      target <- (oget control).`bgm_operation;
      answer <- true;
      remaining <- state.`bps_operations;
      while (remaining <> [] /\ answer) {
        candidate <- head witness remaining;
        remaining <- behead remaining;
        if (beekem_operation_precedes candidate target) {
          contained <@ in_history_operation(candidate, recipient);
          if (! contained) {
            answer <- false;
          }
        }
      }
    }
    return answer;
  }

  proc add_ready(
    sender : beekem_user,
    counter : beekem_counter,
    recipient : beekem_user
  ) : bool = {
    var control : beekem_generated_message option;
    var target : beekem_operation;
    var remaining : beekem_operation list;
    var candidate : beekem_operation;
    var decrypts : bool;
    var answer : bool;

    control <- state.`bps_messages (sender, counter);
    answer <- false;
    if (control <> None /\
        state.`bps_add_targets (sender, counter) = Some recipient) {
      target <- (oget control).`bgm_operation;
      answer <- true;
      remaining <- state.`bps_operations;
      while (remaining <> [] /\ answer) {
        candidate <- head witness remaining;
        remaining <- behead remaining;
        if (beekem_operation_precedes candidate target) {
          decrypts <@ should_decrypt_operation(candidate, recipient);
          if (decrypts /\
              ! state.`bps_delivery_marks
                  (candidate.`bo_author,
                   candidate.`bo_author_counter,
                   recipient)) {
            answer <- false;
          }
        }
      }
    }
    return answer;
  }

  proc adds_member(
    sender : beekem_user,
    counter : beekem_counter,
    recipient : beekem_user
  ) : bool = {
    var control : beekem_generated_message option;
    var history : beekem_operation list;
    var extended : beekem_operation list;
    var before_members : beekem_user fset;
    var after_members : beekem_user fset;
    var remaining : beekem_user list;
    var candidate : beekem_user;
    var answer : bool;

    control <- state.`bps_messages (sender, counter);
    answer <- false;
    if (control <> None) {
      history <@ operations_in_history(recipient);
      extended <- rcons history (oget control).`bgm_operation;
      before_members <- dgm history;
      after_members <- dgm extended;
      remaining <- elems after_members;
      while (remaining <> [] /\ ! answer) {
        candidate <- head witness remaining;
        remaining <- behead remaining;
        if (candidate \notin before_members) {
          answer <- true;
        }
      }
    }
    return answer;
  }

  proc create_group(
    creator : beekem_user,
    initial_members : beekem_user fset
  ) : bool = {
    var actor_frontier : beekem_operation_id fset;
    var creator_state : beekem_member_state option;
    var result : beekem_protocol_result;
    var counter : beekem_counter;
    var operation : beekem_operation_id option;
    var accepted : bool;
    var rejection : beekem_query_rejection option;

    actor_frontier <@ frontier(creator);
    creator_state <- state.`bps_member_states creator;
    result <- witness;
    counter <- BeeKemCounter 1;
    operation <- None;
    accepted <- true;
    rejection <- None;

    if (state.`bps_operations <> []) {
      accepted <- false;
      rejection <- Some BeeRejectAlreadyCreated;
    }
    if (accepted /\ creator \in initial_members) {
      accepted <- false;
      rejection <- Some BeeRejectCreatorInInitialSet;
    }
    if (accepted /\ creator_state = None) {
      accepted <- false;
      rejection <- Some BeeRejectInvalidMember;
    }

    if (accepted) {
      result <@ P.create(oget creator_state, initial_members);
      if (! beekem_member_retention_valid state.`bps_kappa result.`bpr_state) {
        protocol_consistency_failure <- true;
      }
      if (result.`bpr_control = None \/
          beekem_secret_output_is_undefined result.`bpr_secret) {
        protocol_consistency_failure <- true;
      }

      state <-
        {| state with
           bps_member_states =
             beekem_member_state_map_set state.`bps_member_states
               creator (Some result.`bpr_state);
           bps_counters =
             beekem_counter_map_set state.`bps_counters creator 1;
           bps_member_addition_count =
             state.`bps_member_addition_count + size (elems initial_members) |};

      if (result.`bpr_control <> None) {
        operation <- beekem_control_operation_id result.`bpr_control;
        install_control(
          creator,
          counter,
          oget result.`bpr_control,
          result.`bpr_secret,
          true,
          None
        );
      }
    }

    record_query(
      BeeQueryCreate,
      creator,
      None,
      if accepted then Some counter else None,
      operation,
      actor_frontier,
      fset0,
      accepted,
      rejection
    );
    return accepted;
  }

  (* Typed wrappers below expose Add and Remove separately, while this shared
     procedure is the exact Figure 8 MODUSER transition. *)
  proc modify_user(
    adding : bool,
    actor : beekem_user,
    target : beekem_user
  ) : bool = {
    var query_kind : beekem_query_kind;
    var actor_frontier : beekem_operation_id fset;
    var target_frontier : beekem_operation_id fset;
    var member : bool;
    var actor_state : beekem_member_state option;
    var result : beekem_protocol_result;
    var counter_value : int;
    var counter : beekem_counter;
    var operation : beekem_operation_id option;
    var accepted : bool;
    var rejection : beekem_query_rejection option;

    query_kind <- if adding then BeeQueryAdd else BeeQueryRemove;
    actor_frontier <@ frontier(actor);
    target_frontier <@ frontier(target);
    member <@ valid_member(actor);
    actor_state <- state.`bps_member_states actor;
    result <- witness;
    counter_value <- state.`bps_counters actor + 1;
    counter <- beekem_counter_value counter_value;
    operation <- None;
    accepted <- true;
    rejection <- None;

    if (! member) {
      accepted <- false;
      rejection <- Some BeeRejectInvalidMember;
    }
    if (accepted /\ actor = target) {
      accepted <- false;
      rejection <- Some BeeRejectSelfModification;
    }
    if (accepted /\ actor_state = None) {
      accepted <- false;
      rejection <- Some BeeRejectInvalidMember;
    }

    if (accepted) {
      if (adding) {
        result <@ P.add(oget actor_state, target);
      } else {
        result <@ P.remove_member(oget actor_state, target);
      }

      if (! beekem_member_retention_valid state.`bps_kappa result.`bpr_state) {
        protocol_consistency_failure <- true;
      }
      if (result.`bpr_control = None \/
          beekem_secret_output_is_undefined result.`bpr_secret) {
        protocol_consistency_failure <- true;
      }

      state <-
        {| state with
           bps_member_states =
             beekem_member_state_map_set state.`bps_member_states
               actor (Some result.`bpr_state);
           bps_counters =
             beekem_counter_map_set
               state.`bps_counters actor counter_value;
           bps_member_addition_count =
             state.`bps_member_addition_count + (if adding then 1 else 0) |};

      if (result.`bpr_control <> None) {
        operation <- beekem_control_operation_id result.`bpr_control;
        install_control(
          actor,
          counter,
          oget result.`bpr_control,
          result.`bpr_secret,
          ! adding,
          if adding then Some target else None
        );
      }
    }

    record_query(
      query_kind,
      actor,
      Some target,
      if accepted then Some counter else None,
      operation,
      actor_frontier,
      target_frontier,
      accepted,
      rejection
    );
    return accepted;
  }

  proc add_member(
    actor : beekem_user,
    target : beekem_user
  ) : bool = {
    var accepted : bool;
    accepted <@ modify_user(true, actor, target);
    return accepted;
  }

  proc remove_member(
    actor : beekem_user,
    target : beekem_user
  ) : bool = {
    var accepted : bool;
    accepted <@ modify_user(false, actor, target);
    return accepted;
  }

  proc send_update(actor : beekem_user) : bool = {
    var actor_frontier : beekem_operation_id fset;
    var member : bool;
    var actor_state : beekem_member_state option;
    var result : beekem_protocol_result;
    var counter_value : int;
    var counter : beekem_counter;
    var operation : beekem_operation_id option;
    var accepted : bool;
    var rejection : beekem_query_rejection option;

    actor_frontier <@ frontier(actor);
    member <@ valid_member(actor);
    actor_state <- state.`bps_member_states actor;
    result <- witness;
    counter_value <- state.`bps_counters actor + 1;
    counter <- beekem_counter_value counter_value;
    operation <- None;
    accepted <- true;
    rejection <- None;

    if (! member \/ actor_state = None) {
      accepted <- false;
      rejection <- Some BeeRejectInvalidMember;
    }

    if (accepted) {
      result <@ P.update(oget actor_state);
      if (! beekem_member_retention_valid state.`bps_kappa result.`bpr_state) {
        protocol_consistency_failure <- true;
      }
      if (result.`bpr_control = None \/
          beekem_secret_output_is_undefined result.`bpr_secret) {
        protocol_consistency_failure <- true;
      }

      state <-
        {| state with
           bps_member_states =
             beekem_member_state_map_set state.`bps_member_states
               actor (Some result.`bpr_state);
           bps_counters =
             beekem_counter_map_set
               state.`bps_counters actor counter_value |};

      if (result.`bpr_control <> None) {
        operation <- beekem_control_operation_id result.`bpr_control;
        install_control(
          actor,
          counter,
          oget result.`bpr_control,
          result.`bpr_secret,
          true,
          None
        );
      }
    }

    record_query(
      BeeQuerySendUpdate,
      actor,
      None,
      if accepted then Some counter else None,
      operation,
      actor_frontier,
      fset0,
      accepted,
      rejection
    );
    return accepted;
  }

  proc deliver(
    sender : beekem_user,
    counter : beekem_counter,
    recipient : beekem_user
  ) : bool = {
    var actor_frontier : beekem_operation_id fset;
    var target_frontier : beekem_operation_id fset;
    var control : beekem_generated_message option;
    var operation : beekem_operation_id option;
    var already_delivered : bool;
    var receives : bool;
    var causal : bool;
    var ready_for_add : bool;
    var recipient_state : beekem_member_state option;
    var direct : beekem_direct_message option;
    var result : beekem_process_result;
    var decrypts : bool;
    var message_adds_member : bool;
    var must_respond : bool;
    var expected_secret : beekem_secret_output;
    var sender_secret : beekem_secret_output;
    var response_counter_value : int;
    var response_counter : beekem_counter;
    var response_operation : beekem_operation_id option;
    var recipient_frontier_after : beekem_operation_id fset;
    var accepted : bool;
    var rejection : beekem_query_rejection option;

    actor_frontier <@ frontier(sender);
    target_frontier <@ frontier(recipient);
    control <- state.`bps_messages (sender, counter);
    operation <- beekem_control_operation_id control;
    already_delivered <- false;
    receives <- false;
    causal <- false;
    ready_for_add <- false;
    recipient_state <- state.`bps_member_states recipient;
    direct <- state.`bps_direct_messages (sender, counter, recipient);
    result <- witness;
    decrypts <- false;
    message_adds_member <- false;
    must_respond <- false;
    expected_secret <- state.`bps_secrets (sender, counter);
    sender_secret <- BeeSecretNoOutput;
    response_counter_value <- 0;
    response_counter <- BeeKemCounter 0;
    response_operation <- None;
    recipient_frontier_after <- target_frontier;
    accepted <- true;
    rejection <- None;

    if (control = None) {
      accepted <- false;
      rejection <- Some BeeRejectMissingControlMessage;
    }
    if (accepted) {
      already_delivered <@ in_history(sender, counter, recipient);
      if (already_delivered) {
        accepted <- false;
        rejection <- Some BeeRejectAlreadyInHistory;
      }
    }
    if (accepted) {
      receives <@ should_receive(sender, counter, recipient);
      if (! receives) {
        accepted <- false;
        rejection <- Some BeeRejectShouldNotReceive;
      }
    }
    if (accepted) {
      causal <@ causally_ready(sender, counter, recipient);
      ready_for_add <@ add_ready(sender, counter, recipient);
      if (! causal /\ ! ready_for_add) {
        accepted <- false;
        rejection <- Some BeeRejectCausallyUnready;
      }
    }
    if (accepted /\ recipient_state = None) {
      accepted <- false;
      rejection <- Some BeeRejectInvalidMember;
    }

    if (accepted) {
      decrypts <@ should_decrypt(sender, counter, recipient);
      message_adds_member <@ adds_member(sender, counter, recipient);
      result <@ P.process(
        oget recipient_state,
        sender,
        oget control,
        direct
      );
      if (! beekem_member_retention_valid state.`bps_kappa result.`bxr_state) {
        protocol_consistency_failure <- true;
      }

      state <-
        {| state with
           bps_member_states =
             beekem_member_state_map_set state.`bps_member_states
               recipient (Some result.`bxr_state) |};

      sender_secret <- result.`bxr_sender_secret;
      if (decrypts) {
        if (sender_secret <> expected_secret) {
          protocol_consistency_failure <- true;
        }
      } else {
        if (! beekem_secret_output_is_undefined sender_secret) {
          protocol_consistency_failure <- true;
        }
      }

      must_respond <-
        (state.`bps_needs_responses (sender, counter) /\ decrypts) \/
        message_adds_member;
      if (must_respond /\
          (result.`bxr_control = None \/
           beekem_secret_output_is_undefined result.`bxr_response_secret)) {
        protocol_consistency_failure <- true;
      }

      if (result.`bxr_control <> None) {
        response_counter_value <- state.`bps_counters recipient + 1;
        response_counter <- beekem_counter_value response_counter_value;
        state <-
          {| state with
             bps_counters =
               beekem_counter_map_set state.`bps_counters
                 recipient response_counter_value |};
        response_operation <-
          beekem_control_operation_id result.`bxr_control;
        install_control(
          recipient,
          response_counter,
          oget result.`bxr_control,
          result.`bxr_response_secret,
          false,
          None
        );
      }

      state <-
        {| state with
           bps_delivery_marks =
             beekem_delivery_mark_map_set state.`bps_delivery_marks
               (sender, counter, recipient) true |};
      recipient_frontier_after <@ frontier(recipient);
      state <-
        {| state with
           bps_deliveries =
             rcons state.`bps_deliveries
               {| bd_operation = (oget control).`bgm_operation.`bo_id;
                  bd_sender = sender;
                  bd_recipient = recipient;
                  bd_recipient_frontier_before = target_frontier;
                  bd_recipient_frontier_after = recipient_frontier_after;
                  bd_recipient_secret = sender_secret;
                  bd_response_operation = response_operation |} |};
    }

    record_query(
      BeeQueryDeliver,
      sender,
      Some recipient,
      Some counter,
      operation,
      actor_frontier,
      target_frontier,
      accepted,
      rejection
    );
    return accepted;
  }

  proc reveal(
    sender : beekem_user,
    counter : beekem_counter
  ) : beekem_secret_output = {
    var actor_frontier : beekem_operation_id fset;
    var secret : beekem_secret_output;
    var accepted : bool;
    var rejection : beekem_query_rejection option;

    actor_frontier <@ frontier(sender);
    secret <- state.`bps_secrets (sender, counter);
    accepted <- true;
    rejection <- None;

    if (! beekem_secret_output_is_value secret) {
      accepted <- false;
      rejection <- Some BeeRejectMissingSecret;
    }
    if (accepted /\ state.`bps_challenge_marks (sender, counter)) {
      accepted <- false;
      rejection <- Some BeeRejectAlreadyChallengedOrRevealed;
    }

    if (accepted) {
      state <-
        {| state with
           bps_challenge_marks =
             beekem_challenge_mark_map_set state.`bps_challenge_marks
               (sender, counter) true |};
    }

    record_query(
      BeeQueryReveal,
      sender,
      None,
      Some counter,
      beekem_control_operation_id
        (state.`bps_messages (sender, counter)),
      actor_frontier,
      fset0,
      accepted,
      rejection
    );
    return if accepted then secret else BeeSecretNoOutput;
  }

  (* This procedure performs the stateful admission half of CHALLENGE.  The
     hidden-bit game later samples the random branch and uses this returned real
     secret; the adversary never calls this helper directly. *)
  proc open_challenge(
    sender : beekem_user,
    counter : beekem_counter
  ) : beekem_secret_output = {
    var actor_frontier : beekem_operation_id fset;
    var secret : beekem_secret_output;
    var accepted : bool;
    var rejection : beekem_query_rejection option;

    actor_frontier <@ frontier(sender);
    secret <- state.`bps_secrets (sender, counter);
    accepted <- true;
    rejection <- None;

    if (! beekem_secret_output_is_value secret) {
      accepted <- false;
      rejection <- Some BeeRejectMissingSecret;
    }
    if (accepted /\ state.`bps_challenge_marks (sender, counter)) {
      accepted <- false;
      rejection <- Some BeeRejectAlreadyChallengedOrRevealed;
    }

    if (accepted) {
      state <-
        {| state with
           bps_challenge_marks =
             beekem_challenge_mark_map_set state.`bps_challenge_marks
               (sender, counter) true;
           bps_challenge_count = state.`bps_challenge_count + 1 |};
    }

    record_query(
      BeeQueryChallenge,
      sender,
      None,
      Some counter,
      beekem_control_operation_id
        (state.`bps_messages (sender, counter)),
      actor_frontier,
      fset0,
      accepted,
      rejection
    );
    return if accepted then secret else BeeSecretNoOutput;
  }

  proc compromise(
    id : beekem_user
  ) : beekem_member_state option = {
    var actor_frontier : beekem_operation_id fset;
    var compromised : beekem_member_state option;

    actor_frontier <@ frontier(id);
    compromised <- state.`bps_member_states id;
    record_query(
      BeeQueryCompromise,
      id,
      None,
      None,
      None,
      actor_frontier,
      fset0,
      compromised <> None,
      if compromised = None
      then Some BeeRejectInvalidMember
      else None
    );
    return compromised;
  }
}.
