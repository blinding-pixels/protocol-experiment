require import AllCore List FSet.
require import ProtocolTypes.
require import BeeKemTypes BeeKemQueryLog BeeKemProtocol BeeKemKiGame.
require import BeeKemGameWitnesses LiveBeeKemAuthoritativeTypes.

(* Application requests are translated to the canonical BeeKEM oracle without
   changing BeeKEM's game, hidden bit, challenge sampler, state, or query log.
   The adapter keeps a separate application-side audit trail and a bijective
   address registry.  Canonical rejection reasons remain in the authoritative
   challenger log; adapter-only failures are named below. *)
type authoritative_adapter_rejection = [
  | AdapterRejectUnmappedActor
  | AdapterRejectUnmappedTarget
  | AdapterRejectUnmappedInitialMember
  | AdapterRejectUnknownNode
  | AdapterRejectUndeliveredNode
  | AdapterRejectMissingControl
  | AdapterRejectAddressCollision
].

type authoritative_adapter_query_kind = [
  | AdapterCreateQuery of principal & principal fset
  | AdapterAddQuery of principal & principal
  | AdapterRemoveQuery of principal & principal
  | AdapterUpdateQuery of principal
  | AdapterDeliverQuery of node_id & principal
  | AdapterRevealQuery of principal & node_id
  | AdapterChallengeQuery of principal & node_id
  | AdapterCompromiseQuery of principal
].

type authoritative_adapter_query = {
  aaq_kind : authoritative_adapter_query_kind;
  aaq_forwarded : bool;
  aaq_canonical_query : beekem_query_id option;
  aaq_accepted : bool;
  aaq_node : node_id option;
  aaq_address : application_beekem_address option;
  aaq_control : beekem_generated_message option;
  aaq_direct : beekem_direct_message option;
  aaq_output : authoritative_application_root_result option;
  aaq_compromise : beekem_member_state option;
  aaq_adapter_rejection : authoritative_adapter_rejection option
}.

type authoritative_adapter_query_log = authoritative_adapter_query list.

type application_counter_registry = principal -> int.
type application_digest_registry = node_id -> authorization_digest option.
type application_delivery_registry = principal -> node_id -> bool.

op empty_application_counter_registry : application_counter_registry =
  fun _ => 0.

op application_counter_registry_put
    (registry : application_counter_registry)
    (member : principal)
    (value : int) : application_counter_registry =
  fun candidate => if candidate = member then value else registry candidate.

op empty_application_digest_registry : application_digest_registry =
  fun _ => None.

op application_digest_registry_put
    (registry : application_digest_registry)
    (node : node_id)
    (digest : authorization_digest option) : application_digest_registry =
  fun candidate => if candidate = node then digest else registry candidate.

op empty_application_delivery_registry : application_delivery_registry =
  fun _ _ => false.

op application_delivery_registry_put
    (registry : application_delivery_registry)
    (member : principal)
    (node : node_id)
    (value : bool) : application_delivery_registry =
  fun candidate_member candidate_node =>
    if candidate_member = member /\ candidate_node = node
    then value
    else registry candidate_member candidate_node.

op application_user_list_of_principals
    (registry : application_user_registry)
    (members : principal list) : beekem_user list option =
  with members = [] => Some []
  with members = member :: rest =>
    let user = registry.`aur_user_of member in
    let mapped_rest = application_user_list_of_principals registry rest in
    if user = None \/ mapped_rest = None
    then None
    else Some (oget user :: oget mapped_rest).

op application_users_of_principals
    (registry : application_user_registry)
    (members : principal fset) : beekem_user fset option =
  let mapped = application_user_list_of_principals registry (elems members) in
  if mapped = None then None else Some (oflist (oget mapped)).

op authoritative_adapter_control_matches
    (group : beekem_group)
    (user : beekem_user)
    (counter : beekem_counter)
    (kind : beekem_operation_kind)
    (target : beekem_user option)
    (control : beekem_generated_message) : bool =
  control.`bgm_operation.`bo_group = group /\
  control.`bgm_operation.`bo_author = user /\
  control.`bgm_operation.`bo_author_counter = counter /\
  control.`bgm_operation.`bo_kind = kind /\
  control.`bgm_operation.`bo_target = target.

op authoritative_adapter_query_position
    (forwarded_count : int) : beekem_query_id =
  BeeKemQueryId (forwarded_count + 1).

type authoritative_adapter_step_result = {
  aas_accepted : bool;
  aas_node : node_id option;
  aas_address : application_beekem_address option;
  aas_control : beekem_generated_message option;
  aas_output : authoritative_application_root_result option;
  aas_canonical_query : beekem_query_id option;
  aas_runtime_fault : bool
}.

type authoritative_adapter_delivery_result = {
  aadr_accepted : bool;
  aadr_control : beekem_generated_message option;
  aadr_direct : beekem_direct_message option;
  aadr_response_node : node_id option;
  aadr_canonical_query : beekem_query_id option;
  aadr_runtime_fault : bool
}.

type authoritative_adapter_output_result = {
  aaor_forwarded : bool;
  aaor_output : authoritative_application_root_result option;
  aaor_address : application_beekem_address option;
  aaor_canonical_query : beekem_query_id option;
  aaor_runtime_fault : bool
}.

type authoritative_adapter_compromise_result = {
  aacr_forwarded : bool;
  aacr_state : beekem_member_state option;
  aacr_frontier : beekem_operation_id fset;
  aacr_canonical_query : beekem_query_id option;
  aacr_runtime_fault : bool
}.

module AuthoritativeApplicationBeeKemAdapter(
  O : BEEKEM_KI_ORACLES
) = {
  var users : application_user_registry
  var document : document_id
  var group : beekem_group
  var addresses : application_beekem_address_registry
  var counters : application_counter_registry
  var digests : application_digest_registry
  var delivered : application_delivery_registry
  var next_node_value : int
  var forwarded_count : int
  var queries : authoritative_adapter_query_log
  var runtime_fault : bool

  proc init(
    registry : application_user_registry,
    application_document : document_id
  ) : unit = {
    users <- registry;
    document <- application_document;
    group <- application_group_of_document application_document;
    addresses <- empty_application_beekem_address_registry;
    counters <- empty_application_counter_registry;
    digests <- empty_application_digest_registry;
    delivered <- empty_application_delivery_registry;
    next_node_value <- 1;
    forwarded_count <- 0;
    queries <- [];
    runtime_fault <- ! application_user_registry_round_trip registry;
  }

  proc record(query : authoritative_adapter_query) : unit = {
    queries <- rcons queries query;
  }

  proc install_control(
    member : principal,
    user : beekem_user,
    counter : beekem_counter,
    expected_kind : beekem_operation_kind,
    expected_target : beekem_user option,
    digest : authorization_digest option,
    control : beekem_generated_message
  ) : node_id option = {
    var node : node_id;
    var address : application_beekem_address;
    var exact : bool;
    var fresh : bool;
    var answer : node_id option;

    node <- NodeId next_node_value;
    address <-
      {| aba_node = node;
         aba_principal = member;
         aba_user = user;
         aba_counter = counter;
         aba_operation = control.`bgm_operation.`bo_id |};
    exact <- authoritative_adapter_control_matches
      group user counter expected_kind expected_target control;
    fresh <- application_beekem_address_fresh addresses address;
    answer <- None;

    if (exact /\ fresh) {
      addresses <- application_beekem_address_registry_bind addresses address;
      digests <- application_digest_registry_put digests node digest;
      delivered <- application_delivery_registry_put delivered member node true;
      next_node_value <- next_node_value + 1;
      answer <- Some node;
    } else {
      runtime_fault <- true;
    }
    return answer;
  }

  proc create_group(
    creator : principal,
    initial_members : principal fset,
    digest : authorization_digest
  ) : authoritative_adapter_step_result = {
    var user : beekem_user option;
    var mapped_members : beekem_user fset option;
    var canonical_query : beekem_query_id option;
    var counter_value : int;
    var counter : beekem_counter;
    var accepted : bool;
    var control : beekem_generated_message option;
    var node : node_id option;
    var address : application_beekem_address option;
    var output : authoritative_application_root_result option;
    var rejection : authoritative_adapter_rejection option;

    user <- users.`aur_user_of creator;
    mapped_members <- application_users_of_principals users initial_members;
    canonical_query <- None;
    counter_value <- counters creator + 1;
    counter <- BeeKemCounter counter_value;
    accepted <- false;
    control <- None;
    node <- None;
    address <- None;
    output <- None;
    rejection <- None;

    if (user = None) {
      rejection <- Some AdapterRejectUnmappedActor;
    } else if (mapped_members = None) {
      rejection <- Some AdapterRejectUnmappedInitialMember;
    } else {
      canonical_query <- Some (authoritative_adapter_query_position forwarded_count);
      forwarded_count <- forwarded_count + 1;
      accepted <@ O.create_group(oget user, oget mapped_members);
      if (accepted) {
        counters <- application_counter_registry_put counters creator counter_value;
        control <@ O.get_control_message(oget user, counter);
        if (control = None) {
          runtime_fault <- true;
          rejection <- Some AdapterRejectMissingControl;
        } else {
          output <- Some
            (authoritative_application_root_result_of_beekem
              (oget control).`bgm_sender_secret);
          node <@ install_control(
            creator, oget user, counter, BeeCreate, None,
            Some digest, oget control
          );
          if (node <> None) {
            address <- addresses.`abar_by_node (oget node);
          } else {
            rejection <- Some AdapterRejectAddressCollision;
          }
        }
      }
    }

    record(
      {| aaq_kind = AdapterCreateQuery creator initial_members;
         aaq_forwarded = canonical_query <> None;
         aaq_canonical_query = canonical_query;
         aaq_accepted = accepted;
         aaq_node = node;
         aaq_address = address;
         aaq_control = control;
         aaq_direct = None;
         aaq_output = output;
         aaq_compromise = None;
         aaq_adapter_rejection = rejection |}
    );
    return
      {| aas_accepted = accepted;
         aas_node = node;
         aas_address = address;
         aas_control = control;
         aas_output = output;
         aas_canonical_query = canonical_query;
         aas_runtime_fault = runtime_fault |};
  }

  proc add_member(
    author : principal,
    target : principal,
    digest : authorization_digest
  ) : authoritative_adapter_step_result = {
    var user : beekem_user option;
    var target_user : beekem_user option;
    var canonical_query : beekem_query_id option;
    var counter_value : int;
    var counter : beekem_counter;
    var accepted : bool;
    var control : beekem_generated_message option;
    var node : node_id option;
    var address : application_beekem_address option;
    var output : authoritative_application_root_result option;
    var rejection : authoritative_adapter_rejection option;

    user <- users.`aur_user_of author;
    target_user <- users.`aur_user_of target;
    canonical_query <- None;
    counter_value <- counters author + 1;
    counter <- BeeKemCounter counter_value;
    accepted <- false;
    control <- None;
    node <- None;
    address <- None;
    output <- None;
    rejection <- None;

    if (user = None) {
      rejection <- Some AdapterRejectUnmappedActor;
    } else if (target_user = None) {
      rejection <- Some AdapterRejectUnmappedTarget;
    } else {
      canonical_query <- Some (authoritative_adapter_query_position forwarded_count);
      forwarded_count <- forwarded_count + 1;
      accepted <@ O.add_member(oget user, oget target_user);
      if (accepted) {
        counters <- application_counter_registry_put counters author counter_value;
        control <@ O.get_control_message(oget user, counter);
        if (control = None) {
          runtime_fault <- true;
          rejection <- Some AdapterRejectMissingControl;
        } else {
          output <- Some
            (authoritative_application_root_result_of_beekem
              (oget control).`bgm_sender_secret);
          node <@ install_control(
            author, oget user, counter, BeeAdd, target_user,
            Some digest, oget control
          );
          if (node <> None) {
            address <- addresses.`abar_by_node (oget node);
          } else {
            rejection <- Some AdapterRejectAddressCollision;
          }
        }
      }
    }

    record(
      {| aaq_kind = AdapterAddQuery author target;
         aaq_forwarded = canonical_query <> None;
         aaq_canonical_query = canonical_query;
         aaq_accepted = accepted;
         aaq_node = node;
         aaq_address = address;
         aaq_control = control;
         aaq_direct = None;
         aaq_output = output;
         aaq_compromise = None;
         aaq_adapter_rejection = rejection |}
    );
    return
      {| aas_accepted = accepted;
         aas_node = node;
         aas_address = address;
         aas_control = control;
         aas_output = output;
         aas_canonical_query = canonical_query;
         aas_runtime_fault = runtime_fault |};
  }

  proc remove_member(
    author : principal,
    target : principal,
    digest : authorization_digest
  ) : authoritative_adapter_step_result = {
    var user : beekem_user option;
    var target_user : beekem_user option;
    var canonical_query : beekem_query_id option;
    var counter_value : int;
    var counter : beekem_counter;
    var accepted : bool;
    var control : beekem_generated_message option;
    var node : node_id option;
    var address : application_beekem_address option;
    var output : authoritative_application_root_result option;
    var rejection : authoritative_adapter_rejection option;

    user <- users.`aur_user_of author;
    target_user <- users.`aur_user_of target;
    canonical_query <- None;
    counter_value <- counters author + 1;
    counter <- BeeKemCounter counter_value;
    accepted <- false;
    control <- None;
    node <- None;
    address <- None;
    output <- None;
    rejection <- None;

    if (user = None) {
      rejection <- Some AdapterRejectUnmappedActor;
    } else if (target_user = None) {
      rejection <- Some AdapterRejectUnmappedTarget;
    } else {
      canonical_query <- Some (authoritative_adapter_query_position forwarded_count);
      forwarded_count <- forwarded_count + 1;
      accepted <@ O.remove_member(oget user, oget target_user);
      if (accepted) {
        counters <- application_counter_registry_put counters author counter_value;
        control <@ O.get_control_message(oget user, counter);
        if (control = None) {
          runtime_fault <- true;
          rejection <- Some AdapterRejectMissingControl;
        } else {
          output <- Some
            (authoritative_application_root_result_of_beekem
              (oget control).`bgm_sender_secret);
          node <@ install_control(
            author, oget user, counter, BeeRemove, target_user,
            Some digest, oget control
          );
          if (node <> None) {
            address <- addresses.`abar_by_node (oget node);
          } else {
            rejection <- Some AdapterRejectAddressCollision;
          }
        }
      }
    }

    record(
      {| aaq_kind = AdapterRemoveQuery author target;
         aaq_forwarded = canonical_query <> None;
         aaq_canonical_query = canonical_query;
         aaq_accepted = accepted;
         aaq_node = node;
         aaq_address = address;
         aaq_control = control;
         aaq_direct = None;
         aaq_output = output;
         aaq_compromise = None;
         aaq_adapter_rejection = rejection |}
    );
    return
      {| aas_accepted = accepted;
         aas_node = node;
         aas_address = address;
         aas_control = control;
         aas_output = output;
         aas_canonical_query = canonical_query;
         aas_runtime_fault = runtime_fault |};
  }

  proc send_update(
    author : principal,
    digest : authorization_digest
  ) : authoritative_adapter_step_result = {
    var user : beekem_user option;
    var canonical_query : beekem_query_id option;
    var counter_value : int;
    var counter : beekem_counter;
    var accepted : bool;
    var control : beekem_generated_message option;
    var node : node_id option;
    var address : application_beekem_address option;
    var output : authoritative_application_root_result option;
    var rejection : authoritative_adapter_rejection option;

    user <- users.`aur_user_of author;
    canonical_query <- None;
    counter_value <- counters author + 1;
    counter <- BeeKemCounter counter_value;
    accepted <- false;
    control <- None;
    node <- None;
    address <- None;
    output <- None;
    rejection <- None;

    if (user = None) {
      rejection <- Some AdapterRejectUnmappedActor;
    } else {
      canonical_query <- Some (authoritative_adapter_query_position forwarded_count);
      forwarded_count <- forwarded_count + 1;
      accepted <@ O.send_update(oget user);
      if (accepted) {
        counters <- application_counter_registry_put counters author counter_value;
        control <@ O.get_control_message(oget user, counter);
        if (control = None) {
          runtime_fault <- true;
          rejection <- Some AdapterRejectMissingControl;
        } else {
          output <- Some
            (authoritative_application_root_result_of_beekem
              (oget control).`bgm_sender_secret);
          node <@ install_control(
            author, oget user, counter, BeeUpdate, None,
            Some digest, oget control
          );
          if (node <> None) {
            address <- addresses.`abar_by_node (oget node);
          } else {
            rejection <- Some AdapterRejectAddressCollision;
          }
        }
      }
    }

    record(
      {| aaq_kind = AdapterUpdateQuery author;
         aaq_forwarded = canonical_query <> None;
         aaq_canonical_query = canonical_query;
         aaq_accepted = accepted;
         aaq_node = node;
         aaq_address = address;
         aaq_control = control;
         aaq_direct = None;
         aaq_output = output;
         aaq_compromise = None;
         aaq_adapter_rejection = rejection |}
    );
    return
      {| aas_accepted = accepted;
         aas_node = node;
         aas_address = address;
         aas_control = control;
         aas_output = output;
         aas_canonical_query = canonical_query;
         aas_runtime_fault = runtime_fault |};
  }

  proc deliver(
    node : node_id,
    recipient : principal
  ) : authoritative_adapter_delivery_result = {
    var address : application_beekem_address option;
    var recipient_user : beekem_user option;
    var canonical_query : beekem_query_id option;
    var control : beekem_generated_message option;
    var direct : beekem_direct_message option;
    var accepted : bool;
    var response_counter_value : int;
    var response_counter : beekem_counter;
    var response_control : beekem_generated_message option;
    var response_node : node_id option;
    var rejection : authoritative_adapter_rejection option;

    address <- addresses.`abar_by_node node;
    recipient_user <- users.`aur_user_of recipient;
    canonical_query <- None;
    control <- None;
    direct <- None;
    accepted <- false;
    response_counter_value <- counters recipient + 1;
    response_counter <- BeeKemCounter response_counter_value;
    response_control <- None;
    response_node <- None;
    rejection <- None;

    if (address = None) {
      rejection <- Some AdapterRejectUnknownNode;
    } else if (recipient_user = None) {
      rejection <- Some AdapterRejectUnmappedTarget;
    } else {
      control <@ O.get_control_message(
        (oget address).`aba_user,
        (oget address).`aba_counter
      );
      direct <@ O.get_direct_message(
        (oget address).`aba_user,
        (oget address).`aba_counter,
        oget recipient_user
      );
      canonical_query <- Some (authoritative_adapter_query_position forwarded_count);
      forwarded_count <- forwarded_count + 1;
      accepted <@ O.deliver(
        (oget address).`aba_user,
        (oget address).`aba_counter,
        oget recipient_user
      );
      if (accepted) {
        delivered <- application_delivery_registry_put delivered recipient node true;
        response_control <@ O.get_control_message(
          oget recipient_user,
          response_counter
        );
        if (response_control <> None) {
          counters <- application_counter_registry_put
            counters recipient response_counter_value;
          response_node <@ install_control(
            recipient,
            oget recipient_user,
            response_counter,
            BeeResponse,
            None,
            None,
            oget response_control
          );
        }
      }
    }

    record(
      {| aaq_kind = AdapterDeliverQuery node recipient;
         aaq_forwarded = canonical_query <> None;
         aaq_canonical_query = canonical_query;
         aaq_accepted = accepted;
         aaq_node = Some node;
         aaq_address = address;
         aaq_control = control;
         aaq_direct = direct;
         aaq_output = None;
         aaq_compromise = None;
         aaq_adapter_rejection = rejection |}
    );
    return
      {| aadr_accepted = accepted;
         aadr_control = control;
         aadr_direct = direct;
         aadr_response_node = response_node;
         aadr_canonical_query = canonical_query;
         aadr_runtime_fault = runtime_fault |};
  }

  proc reveal(
    member : principal,
    node : node_id
  ) : authoritative_adapter_output_result = {
    var address : application_beekem_address option;
    var canonical_query : beekem_query_id option;
    var output : beekem_secret_output;
    var mapped_output : authoritative_application_root_result option;
    var rejection : authoritative_adapter_rejection option;

    address <- addresses.`abar_by_node node;
    canonical_query <- None;
    output <- BeeSecretNoOutput;
    mapped_output <- None;
    rejection <- None;

    if (address = None) {
      rejection <- Some AdapterRejectUnknownNode;
    } else if (! delivered member node) {
      rejection <- Some AdapterRejectUndeliveredNode;
    } else {
      canonical_query <- Some (authoritative_adapter_query_position forwarded_count);
      forwarded_count <- forwarded_count + 1;
      output <@ O.reveal(
        (oget address).`aba_user,
        (oget address).`aba_counter
      );
      mapped_output <- Some
        (authoritative_application_root_result_of_beekem output);
    }

    record(
      {| aaq_kind = AdapterRevealQuery member node;
         aaq_forwarded = canonical_query <> None;
         aaq_canonical_query = canonical_query;
         aaq_accepted = mapped_output <> None /\
           mapped_output <> Some AuthoritativeRootNoOutput;
         aaq_node = Some node;
         aaq_address = address;
         aaq_control = None;
         aaq_direct = None;
         aaq_output = mapped_output;
         aaq_compromise = None;
         aaq_adapter_rejection = rejection |}
    );
    return
      {| aaor_forwarded = canonical_query <> None;
         aaor_output = mapped_output;
         aaor_address = address;
         aaor_canonical_query = canonical_query;
         aaor_runtime_fault = runtime_fault |};
  }

  proc challenge(
    member : principal,
    node : node_id
  ) : authoritative_adapter_output_result = {
    var address : application_beekem_address option;
    var canonical_query : beekem_query_id option;
    var output : beekem_secret_output;
    var mapped_output : authoritative_application_root_result option;
    var rejection : authoritative_adapter_rejection option;

    address <- addresses.`abar_by_node node;
    canonical_query <- None;
    output <- BeeSecretNoOutput;
    mapped_output <- None;
    rejection <- None;

    if (address = None) {
      rejection <- Some AdapterRejectUnknownNode;
    } else if (! delivered member node) {
      rejection <- Some AdapterRejectUndeliveredNode;
    } else {
      canonical_query <- Some (authoritative_adapter_query_position forwarded_count);
      forwarded_count <- forwarded_count + 1;
      output <@ O.challenge(
        (oget address).`aba_user,
        (oget address).`aba_counter
      );
      mapped_output <- Some
        (authoritative_application_root_result_of_beekem output);
    }

    record(
      {| aaq_kind = AdapterChallengeQuery member node;
         aaq_forwarded = canonical_query <> None;
         aaq_canonical_query = canonical_query;
         aaq_accepted = mapped_output <> None /\
           mapped_output <> Some AuthoritativeRootNoOutput;
         aaq_node = Some node;
         aaq_address = address;
         aaq_control = None;
         aaq_direct = None;
         aaq_output = mapped_output;
         aaq_compromise = None;
         aaq_adapter_rejection = rejection |}
    );
    return
      {| aaor_forwarded = canonical_query <> None;
         aaor_output = mapped_output;
         aaor_address = address;
         aaor_canonical_query = canonical_query;
         aaor_runtime_fault = runtime_fault |};
  }

  proc compromise(
    member : principal
  ) : authoritative_adapter_compromise_result = {
    var user : beekem_user option;
    var canonical_query : beekem_query_id option;
    var state : beekem_member_state option;
    var frontier : beekem_operation_id fset;
    var rejection : authoritative_adapter_rejection option;

    user <- users.`aur_user_of member;
    canonical_query <- None;
    state <- None;
    frontier <- fset0;
    rejection <- None;

    if (user = None) {
      rejection <- Some AdapterRejectUnmappedActor;
    } else {
      canonical_query <- Some (authoritative_adapter_query_position forwarded_count);
      forwarded_count <- forwarded_count + 1;
      state <@ O.compromise(oget user);
      if (state <> None) {
        frontier <- (oget state).`bms_frontier;
      }
    }

    record(
      {| aaq_kind = AdapterCompromiseQuery member;
         aaq_forwarded = canonical_query <> None;
         aaq_canonical_query = canonical_query;
         aaq_accepted = state <> None;
         aaq_node = None;
         aaq_address = None;
         aaq_control = None;
         aaq_direct = None;
         aaq_output = None;
         aaq_compromise = state;
         aaq_adapter_rejection = rejection |}
    );
    return
      {| aacr_forwarded = canonical_query <> None;
         aacr_state = state;
         aacr_frontier = frontier;
         aacr_canonical_query = canonical_query;
         aacr_runtime_fault = runtime_fault |};
  }
}.

(* Concrete canonical-oracle trace: Create, Update, and Challenge are called
   only through the adapter.  The evidence checks the application node address,
   exact bitstring root, canonical query positions, and canonical challenge
   counter. *)
op authoritative_adapter_witness_digest : authorization_digest =
  AuthorizationDigest 703.

module AuthoritativeAdapterOracleWitness = {
  module O = BeeKemKiOracles(BeeKemWitnessProtocol)
  module Adapter = AuthoritativeApplicationBeeKemAdapter(O)

  proc main() : bool = {
    var created : authoritative_adapter_step_result;
    var updated : authoritative_adapter_step_result;
    var challenged : authoritative_adapter_output_result;

    O.initialize(
      [beekem_witness_user],
      beekem_witness_group,
      1,
      beekem_witness_membership,
      true
    );
    Adapter.init(
      authoritative_adapter_witness_registry,
      authoritative_adapter_witness_document
    );
    created <@ Adapter.create_group(
      authoritative_adapter_witness_principal,
      fset0,
      authoritative_adapter_witness_digest
    );
    updated <@ Adapter.send_update(
      authoritative_adapter_witness_principal,
      authoritative_adapter_witness_digest
    );
    challenged <@ Adapter.challenge(
      authoritative_adapter_witness_principal,
      NodeId 2
    );

    return
         created.`aas_accepted
      /\ created.`aas_node = Some (NodeId 1)
      /\ updated.`aas_accepted
      /\ updated.`aas_node = Some (NodeId 2)
      /\ challenged.`aaor_forwarded
      /\ challenged.`aaor_output =
           Some
             (AuthoritativeRootValue
               (AuthoritativeApplicationRoot [true]))
      /\ Adapter.addresses.`abar_node_of_message
           beekem_witness_user (BeeKemCounter 2) = Some (NodeId 2)
      /\ size Adapter.queries = 3
      /\ size O.Environment.query_log = 3
      /\ O.Environment.state.`bps_challenge_count = 1
      /\ ! Adapter.runtime_fault
      /\ ! O.Environment.protocol_consistency_failure;
  }
}.

lemma authoritative_adapter_oracle_trace_nonvacuous :
  hoare [AuthoritativeAdapterOracleWitness.main : true ==> res].
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
  rewrite /authoritative_adapter_witness_registry
    /application_user_registry_bind /empty_application_user_registry
    /authoritative_adapter_witness_principal
    /authoritative_adapter_witness_document
    /authoritative_adapter_witness_digest
    /application_group_of_document
    /application_user_registry_round_trip
    /application_users_of_principals
    /application_user_list_of_principals
    /empty_application_beekem_address_registry
    /empty_application_counter_registry
    /empty_application_digest_registry
    /empty_application_delivery_registry
    /application_counter_registry_put
    /application_digest_registry_put
    /application_delivery_registry_put
    /authoritative_adapter_query_position
    /authoritative_adapter_control_matches
    /application_beekem_address_fresh
    /application_beekem_address_registry_bind
    /authoritative_application_root_result_of_beekem
    /authoritative_application_root_of_beekem
    /beekem_witness_membership /beekem_witness_initial_member_state
    /beekem_member_retention_valid /beekem_witness_personal_secret
    /beekem_witness_after_create /beekem_witness_after_update
    /beekem_witness_control /beekem_witness_create_operation
    /beekem_witness_update_operation /beekem_witness_operation
    /beekem_control_operation_id /beekem_control_operation
    /beekem_counter_value /beekem_empty_protocol_state
    /beekem_secret_output_is_undefined /beekem_secret_output_is_value
    /beekem_secret_output_value /beekem_operation_precedes_or_equals
    /beekem_operation_precedes.
  by rewrite !inE; smt(size_rcons size_ge0).
qed.
