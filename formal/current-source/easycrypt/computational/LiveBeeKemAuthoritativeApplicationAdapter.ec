require import AllCore List FSet.
require import ProtocolTypes BeeKemTypes BeeKemQueryLog BeeKemKiGame.
require import LiveBeeKemAuthoritativeTypes LiveBeeKemAuthoritativeAdapter.
require import LiveBeeKemAuthoritativeApplicationState.

(* Stateful application translation over the authoritative Figure-8 oracle.
   This module owns only cross-layer identity/address metadata.  It owns no
   BeeKEM protocol state, query log, safety predicate, hidden bit, or random
   sampler. *)
module AuthoritativeApplicationBeeKemCore(
  O : BEEKEM_KI_ORACLES
) = {
  module F = AuthoritativeBeeKemOracleForwarder(O)

  var users : application_user_registry
  var document : document_id
  var group : beekem_group
  var addresses : application_beekem_address_registry
  var counters : application_beekem_counter_store
  var digests : application_beekem_digest_store
  var deliveries : application_beekem_delivery_store
  var attempts : application_beekem_attempt_log
  var forwarded_count : int
  var next_node_value : int
  var runtime_fault : bool

  proc init(
    input_users : application_user_registry,
    input_document : document_id
  ) : unit = {
    users <- input_users;
    document <- input_document;
    group <- application_group_of_document input_document;
    addresses <- empty_application_beekem_address_registry;
    counters <- empty_application_beekem_counter_store;
    digests <- empty_application_beekem_digest_store;
    deliveries <- empty_application_beekem_delivery_store;
    attempts <- [];
    forwarded_count <- 0;
    next_node_value <- 1;
    runtime_fault <- false;
  }

  proc record(attempt : application_beekem_attempt) : unit = {
    attempts <- rcons attempts attempt;
  }

  proc record_local_rejection(
    kind : application_beekem_attempt_kind,
    rejection : application_beekem_mapping_rejection
  ) : unit = {
    record(
      {| aba_kind = kind;
         aba_forwarded = false;
         aba_canonical_query_id = None;
         aba_canonical_accepted = false;
         aba_node = None;
         aba_address = None;
         aba_control = None;
         aba_direct = None;
         aba_secret_output = None;
         aba_root_output = None;
         aba_compromise = None;
         aba_compromise_frontier = fset0;
         aba_mapping_rejection = Some rejection |}
    );
  }

  proc record_step(
    kind : application_beekem_attempt_kind,
    canonical_accepted : bool,
    result : application_beekem_step_result
  ) : unit = {
    record(
      {| aba_kind = kind;
         aba_forwarded = true;
         aba_canonical_query_id = result.`abs_canonical_query_id;
         aba_canonical_accepted = canonical_accepted;
         aba_node = result.`abs_node;
         aba_address = result.`abs_address;
         aba_control = result.`abs_control;
         aba_direct = None;
         aba_secret_output = result.`abs_secret_output;
         aba_root_output = result.`abs_root_output;
         aba_compromise = None;
         aba_compromise_frontier = fset0;
         aba_mapping_rejection = None |}
    );
  }

  proc finish_control(
    actor : principal,
    user : beekem_user,
    counter_value : int,
    digest : authorization_digest option,
    expected_kind : beekem_operation_kind,
    expected_target : beekem_user option,
    query_id : beekem_query_id
  ) : application_beekem_step_result = {
    var counter : beekem_counter;
    var control : beekem_generated_message option;
    var operation : beekem_operation;
    var node : node_id;
    var address : application_beekem_address;
    var control_exact : bool;
    var fresh : bool;
    var output : beekem_secret_output;
    var result : application_beekem_step_result;

    counter <- BeeKemCounter counter_value;
    control <@ F.get_control_message(user, counter);
    operation <- witness;
    node <- witness;
    address <- witness;
    control_exact <- false;
    fresh <- false;
    output <- BeeSecretUndefined;
    result <-
      {| abs_accepted = false;
         abs_node = None;
         abs_address = None;
         abs_control = control;
         abs_secret_output = None;
         abs_root_output = None;
         abs_canonical_query_id = Some query_id;
         abs_runtime_fault = false |};

    if (control = None) {
      runtime_fault <- true;
      result <- {| result with abs_runtime_fault = true |};
    } else {
      operation <- (oget control).`bgm_operation;
      node <- NodeId next_node_value;
      address <-
        {| aba_node = node;
           aba_principal = actor;
           aba_user = user;
           aba_counter = counter;
           aba_operation = operation.`bo_id |};
      control_exact <-
           operation.`bo_group = group
        /\ operation.`bo_author = user
        /\ operation.`bo_author_counter = counter
        /\ operation.`bo_kind = expected_kind
        /\ operation.`bo_target = expected_target;
      fresh <- application_beekem_address_fresh addresses address;
      if (! control_exact \/ ! fresh) {
        runtime_fault <- true;
        result <- {| result with abs_runtime_fault = true |};
      } else {
        output <- (oget control).`bgm_sender_secret;
        addresses <-
          application_beekem_address_registry_bind addresses address;
        digests <- application_beekem_digest_store_put digests node digest;
        deliveries <-
          application_beekem_delivery_store_put deliveries actor node true;
        next_node_value <- next_node_value + 1;
        result <-
          {| abs_accepted = true;
             abs_node = Some node;
             abs_address = Some address;
             abs_control = control;
             abs_secret_output = Some output;
             abs_root_output = Some
               (authoritative_application_root_result_of_beekem output);
             abs_canonical_query_id = Some query_id;
             abs_runtime_fault = false |};
      }
    }
    return result;
  }

  proc create_group(
    creator : principal,
    initial_members : principal fset,
    digest : authorization_digest
  ) : application_beekem_step_result = {
    var creator_user : beekem_user option;
    var mapped_members : beekem_user fset option;
    var query_id : beekem_query_id;
    var canonical_accepted : bool;
    var result : application_beekem_step_result;

    creator_user <- users.`aur_user_of creator;
    mapped_members <- application_beekem_users_of_set users initial_members;
    query_id <- witness;
    canonical_accepted <- false;
    result <-
      {| abs_accepted = false; abs_node = None; abs_address = None;
         abs_control = None; abs_secret_output = None; abs_root_output = None;
         abs_canonical_query_id = None; abs_runtime_fault = false |};

    if (creator_user = None) {
      record_local_rejection(
        ApplicationBeeKemCreateAttempt (creator, initial_members),
        ApplicationBeeKemUnmappedActor
      );
    } else {
      if (mapped_members = None) {
        record_local_rejection(
          ApplicationBeeKemCreateAttempt (creator, initial_members),
          ApplicationBeeKemUnmappedInitialMember
        );
      } else {
        query_id <- application_beekem_next_query_id forwarded_count;
        canonical_accepted <@ F.create_group(
          oget creator_user, oget mapped_members
        );
        forwarded_count <- forwarded_count + 1;
        if (canonical_accepted) {
          counters <- application_beekem_counter_store_put counters creator 1;
          result <@ finish_control(
            creator, oget creator_user, 1, Some digest,
            BeeCreate, None, query_id
          );
        } else {
          result <- {| result with abs_canonical_query_id = Some query_id |};
        }
        record_step(
          ApplicationBeeKemCreateAttempt (creator, initial_members),
          canonical_accepted,
          result
        );
      }
    }
    return result;
  }

  proc add_member(
    actor : principal,
    target : principal,
    digest : authorization_digest
  ) : application_beekem_step_result = {
    var actor_user : beekem_user option;
    var target_user : beekem_user option;
    var counter_value : int;
    var query_id : beekem_query_id;
    var canonical_accepted : bool;
    var result : application_beekem_step_result;

    actor_user <- users.`aur_user_of actor;
    target_user <- users.`aur_user_of target;
    counter_value <- counters actor + 1;
    query_id <- witness;
    canonical_accepted <- false;
    result <-
      {| abs_accepted = false; abs_node = None; abs_address = None;
         abs_control = None; abs_secret_output = None; abs_root_output = None;
         abs_canonical_query_id = None; abs_runtime_fault = false |};

    if (actor_user = None) {
      record_local_rejection(
        ApplicationBeeKemAddAttempt (actor, target),
        ApplicationBeeKemUnmappedActor
      );
    } else {
      if (target_user = None) {
        record_local_rejection(
          ApplicationBeeKemAddAttempt (actor, target),
          ApplicationBeeKemUnmappedTarget
        );
      } else {
        query_id <- application_beekem_next_query_id forwarded_count;
        canonical_accepted <@ F.add_member(oget actor_user, oget target_user);
        forwarded_count <- forwarded_count + 1;
        if (canonical_accepted) {
          counters <-
            application_beekem_counter_store_put counters actor counter_value;
          result <@ finish_control(
            actor, oget actor_user, counter_value, Some digest,
            BeeAdd, Some (oget target_user), query_id
          );
        } else {
          result <- {| result with abs_canonical_query_id = Some query_id |};
        }
        record_step(
          ApplicationBeeKemAddAttempt (actor, target),
          canonical_accepted,
          result
        );
      }
    }
    return result;
  }

  proc remove_member(
    actor : principal,
    target : principal,
    digest : authorization_digest
  ) : application_beekem_step_result = {
    var actor_user : beekem_user option;
    var target_user : beekem_user option;
    var counter_value : int;
    var query_id : beekem_query_id;
    var canonical_accepted : bool;
    var result : application_beekem_step_result;

    actor_user <- users.`aur_user_of actor;
    target_user <- users.`aur_user_of target;
    counter_value <- counters actor + 1;
    query_id <- witness;
    canonical_accepted <- false;
    result <-
      {| abs_accepted = false; abs_node = None; abs_address = None;
         abs_control = None; abs_secret_output = None; abs_root_output = None;
         abs_canonical_query_id = None; abs_runtime_fault = false |};

    if (actor_user = None) {
      record_local_rejection(
        ApplicationBeeKemRemoveAttempt (actor, target),
        ApplicationBeeKemUnmappedActor
      );
    } else {
      if (target_user = None) {
        record_local_rejection(
          ApplicationBeeKemRemoveAttempt (actor, target),
          ApplicationBeeKemUnmappedTarget
        );
      } else {
        query_id <- application_beekem_next_query_id forwarded_count;
        canonical_accepted <@ F.remove_member(
          oget actor_user, oget target_user
        );
        forwarded_count <- forwarded_count + 1;
        if (canonical_accepted) {
          counters <-
            application_beekem_counter_store_put counters actor counter_value;
          result <@ finish_control(
            actor, oget actor_user, counter_value, Some digest,
            BeeRemove, Some (oget target_user), query_id
          );
        } else {
          result <- {| result with abs_canonical_query_id = Some query_id |};
        }
        record_step(
          ApplicationBeeKemRemoveAttempt (actor, target),
          canonical_accepted,
          result
        );
      }
    }
    return result;
  }

  proc send_update(
    actor : principal,
    digest : authorization_digest
  ) : application_beekem_step_result = {
    var actor_user : beekem_user option;
    var counter_value : int;
    var query_id : beekem_query_id;
    var canonical_accepted : bool;
    var result : application_beekem_step_result;

    actor_user <- users.`aur_user_of actor;
    counter_value <- counters actor + 1;
    query_id <- witness;
    canonical_accepted <- false;
    result <-
      {| abs_accepted = false; abs_node = None; abs_address = None;
         abs_control = None; abs_secret_output = None; abs_root_output = None;
         abs_canonical_query_id = None; abs_runtime_fault = false |};

    if (actor_user = None) {
      record_local_rejection(
        ApplicationBeeKemUpdateAttempt actor,
        ApplicationBeeKemUnmappedActor
      );
    } else {
      query_id <- application_beekem_next_query_id forwarded_count;
      canonical_accepted <@ F.send_update(oget actor_user);
      forwarded_count <- forwarded_count + 1;
      if (canonical_accepted) {
        counters <-
          application_beekem_counter_store_put counters actor counter_value;
        result <@ finish_control(
          actor, oget actor_user, counter_value, Some digest,
          BeeUpdate, None, query_id
        );
      } else {
        result <- {| result with abs_canonical_query_id = Some query_id |};
      }
      record_step(
        ApplicationBeeKemUpdateAttempt actor,
        canonical_accepted,
        result
      );
    }
    return result;
  }

  proc deliver(
    node : node_id,
    recipient : principal
  ) : application_beekem_delivery_result = {
    var address : application_beekem_address option;
    var recipient_user : beekem_user option;
    var query_id : beekem_query_id;
    var control : beekem_generated_message option;
    var direct : beekem_direct_message option;
    var canonical_accepted : bool;
    var response_counter_value : int;
    var response_counter : beekem_counter;
    var response_control : beekem_generated_message option;
    var response_step : application_beekem_step_result;
    var response_node : node_id option;
    var result : application_beekem_delivery_result;

    address <- addresses.`abar_by_node node;
    recipient_user <- users.`aur_user_of recipient;
    query_id <- witness;
    control <- None;
    direct <- None;
    canonical_accepted <- false;
    response_counter_value <- 0;
    response_counter <- BeeKemCounter 0;
    response_control <- None;
    response_step <- witness;
    response_node <- None;
    result <-
      {| abd_accepted = false; abd_control = None; abd_direct = None;
         abd_response_node = None; abd_canonical_query_id = None;
         abd_runtime_fault = false |};

    if (address = None) {
      record_local_rejection(
        ApplicationBeeKemDeliverAttempt (node, recipient),
        ApplicationBeeKemUnknownNode
      );
    } else {
      if (recipient_user = None) {
        record_local_rejection(
          ApplicationBeeKemDeliverAttempt (node, recipient),
          ApplicationBeeKemUnmappedTarget
        );
      } else {
        control <@ F.get_control_message(
          (oget address).`aba_user,
          (oget address).`aba_counter
        );
        direct <@ F.get_direct_message(
          (oget address).`aba_user,
          (oget address).`aba_counter,
          oget recipient_user
        );
        query_id <- application_beekem_next_query_id forwarded_count;
        canonical_accepted <@ F.deliver(
          (oget address).`aba_user,
          (oget address).`aba_counter,
          oget recipient_user
        );
        forwarded_count <- forwarded_count + 1;

        if (canonical_accepted) {
          deliveries <-
            application_beekem_delivery_store_put
              deliveries recipient node true;
          if (control = None) {
            runtime_fault <- true;
          }

          response_counter_value <- counters recipient + 1;
          response_counter <- BeeKemCounter response_counter_value;
          response_control <@ F.get_control_message(
            oget recipient_user,
            response_counter
          );
          if (response_control <> None) {
            counters <-
              application_beekem_counter_store_put
                counters recipient response_counter_value;
            response_step <@ finish_control(
              recipient, oget recipient_user, response_counter_value, None,
              BeeResponse, None, query_id
            );
            response_node <- response_step.`abs_node;
          }
        }

        result <-
          {| abd_accepted = canonical_accepted /\ ! runtime_fault;
             abd_control = control;
             abd_direct = direct;
             abd_response_node = response_node;
             abd_canonical_query_id = Some query_id;
             abd_runtime_fault = runtime_fault |};
        record(
          {| aba_kind = ApplicationBeeKemDeliverAttempt (node, recipient);
             aba_forwarded = true;
             aba_canonical_query_id = Some query_id;
             aba_canonical_accepted = canonical_accepted;
             aba_node = Some node;
             aba_address = address;
             aba_control = control;
             aba_direct = direct;
             aba_secret_output = None;
             aba_root_output = None;
             aba_compromise = None;
             aba_compromise_frontier = fset0;
             aba_mapping_rejection = None |}
        );
      }
    }
    return result;
  }

  proc reveal_or_challenge(
    challenging : bool,
    member : principal,
    node : node_id
  ) : application_beekem_output_result = {
    var member_user : beekem_user option;
    var address : application_beekem_address option;
    var query_id : beekem_query_id;
    var output : beekem_secret_output;
    var canonical_accepted : bool;
    var result : application_beekem_output_result;
    var kind : application_beekem_attempt_kind;

    member_user <- users.`aur_user_of member;
    address <- addresses.`abar_by_node node;
    query_id <- witness;
    output <- BeeSecretNoOutput;
    canonical_accepted <- false;
    kind <- if challenging
      then ApplicationBeeKemChallengeAttempt (member, node)
      else ApplicationBeeKemRevealAttempt (member, node);
    result <-
      {| abo_forwarded = false;
         abo_canonical_accepted = false;
         abo_secret_output = None;
         abo_root_output = None;
         abo_address = address;
         abo_canonical_query_id = None;
         abo_runtime_fault = false |};

    if (member_user = None) {
      record_local_rejection(kind, ApplicationBeeKemUnmappedActor);
    } else {
      if (address = None) {
        record_local_rejection(kind, ApplicationBeeKemUnknownNode);
      } else {
        if (! deliveries member node) {
          record_local_rejection(kind, ApplicationBeeKemUndeliveredNode);
        } else {
          query_id <- application_beekem_next_query_id forwarded_count;
          if (challenging) {
            output <@ F.challenge(
              (oget address).`aba_user,
              (oget address).`aba_counter
            );
          } else {
            output <@ F.reveal(
              (oget address).`aba_user,
              (oget address).`aba_counter
            );
          }
          forwarded_count <- forwarded_count + 1;
          canonical_accepted <- beekem_secret_output_is_value output;
          result <-
            {| abo_forwarded = true;
               abo_canonical_accepted = canonical_accepted;
               abo_secret_output = Some output;
               abo_root_output = Some
                 (authoritative_application_root_result_of_beekem output);
               abo_address = address;
               abo_canonical_query_id = Some query_id;
               abo_runtime_fault = false |};
          record(
            {| aba_kind = kind;
               aba_forwarded = true;
               aba_canonical_query_id = Some query_id;
               aba_canonical_accepted = canonical_accepted;
               aba_node = Some node;
               aba_address = address;
               aba_control = None;
               aba_direct = None;
               aba_secret_output = Some output;
               aba_root_output = result.`abo_root_output;
               aba_compromise = None;
               aba_compromise_frontier = fset0;
               aba_mapping_rejection = None |}
          );
        }
      }
    }
    return result;
  }

  proc reveal(
    member : principal,
    node : node_id
  ) : application_beekem_output_result = {
    var result : application_beekem_output_result;
    result <@ reveal_or_challenge(false, member, node);
    return result;
  }

  proc challenge(
    member : principal,
    node : node_id
  ) : application_beekem_output_result = {
    var result : application_beekem_output_result;
    result <@ reveal_or_challenge(true, member, node);
    return result;
  }

  proc compromise(
    member : principal
  ) : application_beekem_compromise_result = {
    var user : beekem_user option;
    var query_id : beekem_query_id;
    var state : beekem_member_state option;
    var frontier : beekem_operation_id fset;
    var result : application_beekem_compromise_result;

    user <- users.`aur_user_of member;
    query_id <- witness;
    state <- None;
    frontier <- fset0;
    result <-
      {| abc_forwarded = false; abc_state = None; abc_frontier = fset0;
         abc_canonical_query_id = None; abc_runtime_fault = false |};

    if (user = None) {
      record_local_rejection(
        ApplicationBeeKemCompromiseAttempt member,
        ApplicationBeeKemUnmappedActor
      );
    } else {
      query_id <- application_beekem_next_query_id forwarded_count;
      state <@ F.compromise(oget user);
      forwarded_count <- forwarded_count + 1;
      if (state <> None) {
        frontier <- (oget state).`bms_frontier;
      }
      result <-
        {| abc_forwarded = true;
           abc_state = state;
           abc_frontier = frontier;
           abc_canonical_query_id = Some query_id;
           abc_runtime_fault = false |};
      record(
        {| aba_kind = ApplicationBeeKemCompromiseAttempt member;
           aba_forwarded = true;
           aba_canonical_query_id = Some query_id;
           aba_canonical_accepted = state <> None;
           aba_node = None;
           aba_address = None;
           aba_control = None;
           aba_direct = None;
           aba_secret_output = None;
           aba_root_output = None;
           aba_compromise = state;
           aba_compromise_frontier = frontier;
           aba_mapping_rejection = None |}
      );
    }
    return result;
  }
}.

(* Public application surface: raw authoritative group secrets never cross this
   interface.  The proof-only Core retains the exact three-way output as
   evidence, while callers receive only the distinct application root wrapper. *)
module type AUTHORITATIVE_APPLICATION_BEEKEM_ORACLE = {
  proc create_group(
    creator : principal,
    initial_members : principal fset,
    digest : authorization_digest
  ) : node_id option

  proc add_member(
    actor : principal,
    target : principal,
    digest : authorization_digest
  ) : node_id option

  proc remove_member(
    actor : principal,
    target : principal,
    digest : authorization_digest
  ) : node_id option

  proc send_update(
    actor : principal,
    digest : authorization_digest
  ) : node_id option

  proc deliver(node : node_id, recipient : principal) : bool

  proc reveal(
    member : principal,
    node : node_id
  ) : authoritative_application_root_result option

  proc challenge(
    member : principal,
    node : node_id
  ) : authoritative_application_root_result option

  proc compromise(member : principal) : beekem_member_state option
}.

module AuthoritativeApplicationBeeKemOracle(
  O : BEEKEM_KI_ORACLES
) = {
  module Core = AuthoritativeApplicationBeeKemCore(O)

  proc init(
    users : application_user_registry,
    document : document_id
  ) : unit = {
    Core.init(users, document);
  }

  proc create_group(
    creator : principal,
    initial_members : principal fset,
    digest : authorization_digest
  ) : node_id option = {
    var result : application_beekem_step_result;
    result <@ Core.create_group(creator, initial_members, digest);
    return if result.`abs_accepted then result.`abs_node else None;
  }

  proc add_member(
    actor : principal,
    target : principal,
    digest : authorization_digest
  ) : node_id option = {
    var result : application_beekem_step_result;
    result <@ Core.add_member(actor, target, digest);
    return if result.`abs_accepted then result.`abs_node else None;
  }

  proc remove_member(
    actor : principal,
    target : principal,
    digest : authorization_digest
  ) : node_id option = {
    var result : application_beekem_step_result;
    result <@ Core.remove_member(actor, target, digest);
    return if result.`abs_accepted then result.`abs_node else None;
  }

  proc send_update(
    actor : principal,
    digest : authorization_digest
  ) : node_id option = {
    var result : application_beekem_step_result;
    result <@ Core.send_update(actor, digest);
    return if result.`abs_accepted then result.`abs_node else None;
  }

  proc deliver(node : node_id, recipient : principal) : bool = {
    var result : application_beekem_delivery_result;
    result <@ Core.deliver(node, recipient);
    return result.`abd_accepted;
  }

  proc reveal(
    member : principal,
    node : node_id
  ) : authoritative_application_root_result option = {
    var result : application_beekem_output_result;
    result <@ Core.reveal(member, node);
    return if result.`abo_canonical_accepted
      then result.`abo_root_output else None;
  }

  proc challenge(
    member : principal,
    node : node_id
  ) : authoritative_application_root_result option = {
    var result : application_beekem_output_result;
    result <@ Core.challenge(member, node);
    return if result.`abo_canonical_accepted
      then result.`abo_root_output else None;
  }

  proc compromise(member : principal) : beekem_member_state option = {
    var result : application_beekem_compromise_result;
    result <@ Core.compromise(member);
    return result.`abc_state;
  }
}.
