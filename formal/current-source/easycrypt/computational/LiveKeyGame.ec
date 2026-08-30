require import AllCore List FSet Distr DBool.
require import ProtocolTypes CanonicalEncoding ProtocolPrimitives AuthorizationState.
require import ProtocolChecks ProtocolOracles AuthorizationAncestry.
require import PrimitiveGames UnauthorizedOriginGame.

import PG.

(* ------------------------------------------------------------------------- *)
(* Deliverable L, checkpoint 1: executable application live-key experiment.   *)
(*                                                                           *)
(* The BeeKEM runtime and key schedule are module parameters, but every        *)
(* protocol transition, delivery decision, reveal exclusion, challenge record,*)
(* compromise record, causal relation, and bee-safe_kappa decision below is    *)
(* computed by the game.  No adversary-supplied safety or authentication bit   *)
(* appears in this interface.                                                  *)
(* ------------------------------------------------------------------------- *)

type beekem_secret = [ BeeKemSecret of int ].
type live_key_label = {
  lkl_protocol_version : int;
  lkl_document_id : document_id;
  lkl_node_id : node_id;
  lkl_authorization_digest : authorization_digest
}.

type live_application_key = [ LiveApplicationKey of int & live_key_label ].

type history_key_label = {
  hkl_protocol_version : int;
  hkl_document_id : document_id;
  hkl_segment_id : segment_id;
  hkl_authorization_digest : authorization_digest
}.

type history_domain_output = [ HistoryDomainOutput of int & history_key_label ].
type history_capability_output = [
  HistoryCapabilityOutput of int & history_key_label & segment_cover
].

type beekem_snapshot = {
  bs_principal : principal;
  bs_generation : int
}.

type beekem_control_kind = [
  | BeeCreate
  | BeeAdd
  | BeeRemove
  | BeeUpdate
].

type beekem_control_message = {
  bcm_node : node_id;
  bcm_kind : beekem_control_kind;
  bcm_author : principal;
  bcm_target : principal option;
  bcm_predecessors : node_id fset;
  bcm_authorization_digest : authorization_digest
}.

type beekem_step_result = {
  bsr_message : beekem_control_message;
  bsr_secret : beekem_secret option
}.

module type BEEKEM_LIVE_RUNTIME = {
  proc init() : unit

  proc create_group(
    creator : principal,
    initial_members : principal fset,
    digest : authorization_digest
  ) : beekem_step_result

  proc add_member(
    author : principal,
    target : principal,
    digest : authorization_digest
  ) : beekem_step_result

  proc remove_member(
    author : principal,
    target : principal,
    digest : authorization_digest
  ) : beekem_step_result

  proc send_update(
    author : principal,
    digest : authorization_digest
  ) : beekem_step_result

  proc deliver(
    message : beekem_control_message,
    recipient : principal
  ) : beekem_secret option

  proc compromise(principal : principal) : beekem_snapshot
}.

module type MULTI_DOMAIN_KEY_SCHEDULE = {
  proc derive_live(
    secret : beekem_secret,
    label : live_key_label
  ) : live_application_key

  proc derive_history(
    secret : beekem_secret,
    label : history_key_label
  ) : history_domain_output

  proc derive_history_capability(
    secret : beekem_secret,
    label : history_key_label,
    cover : segment_cover
  ) : history_capability_output
}.

module type LIVE_KEY_SAMPLER = {
  proc sample(label : live_key_label) : live_application_key
}.

(* The exact public-domain labels used by the application derivation. *)
op live_label_of
    (state : protocol_state)
    (node : node_id)
    (digest : authorization_digest) : live_key_label =
  {| lkl_protocol_version = expected_protocol_version;
     lkl_document_id = state.`ps_document_id;
     lkl_node_id = node;
     lkl_authorization_digest = digest |}.

op history_label_of
    (state : protocol_state)
    (segment : segment_id)
    (digest : authorization_digest) : history_key_label =
  {| hkl_protocol_version = expected_protocol_version;
     hkl_document_id = state.`ps_document_id;
     hkl_segment_id = segment;
     hkl_authorization_digest = digest |}.

(* ------------------------------------------------------------------------- *)
(* Causal graph and per-member delivery state.                                *)
(* ------------------------------------------------------------------------- *)

type causal_relation = node_id -> node_id -> bool.
type control_store = node_id -> beekem_control_message option.
type node_digest_store = node_id -> authorization_digest option.
type delivery_store = principal -> node_id -> bool.
type member_secret_store = principal -> node_id -> beekem_secret option.
type member_head_store = principal -> node_id option.
type active_member_store = principal -> bool.

op empty_causal_relation : causal_relation = fun _ _ => false.
op empty_control_store : control_store = fun _ => None.
op empty_node_digest_store : node_digest_store = fun _ => None.
op empty_delivery_store : delivery_store = fun _ _ => false.
op empty_member_secret_store : member_secret_store = fun _ _ => None.
op empty_member_head_store : member_head_store = fun _ => None.
op empty_active_member_store : active_member_store = fun _ => false.

op control_store_put
    (store : control_store)
    (node : node_id)
    (message : beekem_control_message) : control_store =
  fun candidate => if candidate = node then Some message else store candidate.

op node_digest_store_put
    (store : node_digest_store)
    (node : node_id)
    (digest : authorization_digest) : node_digest_store =
  fun candidate => if candidate = node then Some digest else store candidate.

op delivery_store_put
    (store : delivery_store)
    (recipient : principal)
    (node : node_id)
    (value : bool) : delivery_store =
  fun candidate_recipient candidate_node =>
    if candidate_recipient = recipient /\ candidate_node = node
    then value
    else store candidate_recipient candidate_node.

op member_secret_store_put
    (store : member_secret_store)
    (member : principal)
    (node : node_id)
    (secret : beekem_secret option) : member_secret_store =
  fun candidate_member candidate_node =>
    if candidate_member = member /\ candidate_node = node
    then secret
    else store candidate_member candidate_node.

op member_head_store_put
    (store : member_head_store)
    (member : principal)
    (node : node_id) : member_head_store =
  fun candidate => if candidate = member then Some node else store candidate.

op active_member_store_put
    (store : active_member_store)
    (member : principal)
    (value : bool) : active_member_store =
  fun candidate => if candidate = member then value else store candidate.

op active_member_store_of_set
    (members : principal fset) : active_member_store =
  fun candidate => candidate \in members.

op predecessor_reaches_list
    (relation : causal_relation)
    (left : node_id)
    (predecessors : node_id list) : bool =
  with predecessors = [] => false
  with predecessors = predecessor :: rest =>
       left = predecessor
    \/ relation left predecessor
    \/ predecessor_reaches_list relation left rest.

op causal_relation_extend
    (relation : causal_relation)
    (node : node_id)
    (predecessors : node_id fset) : causal_relation =
  fun left right =>
       relation left right
    \/ (right = node /\
        predecessor_reaches_list relation left (elems predecessors)).

op causally_before
    (relation : causal_relation)
    (left right : node_id) : bool =
  relation left right.

op causally_at_or_before
    (relation : causal_relation)
    (left right : node_id) : bool =
  left = right \/ causally_before relation left right.

op causally_concurrent
    (relation : causal_relation)
    (left right : node_id) : bool =
     left <> right
  /\ ! causally_before relation left right
  /\ ! causally_before relation right left.

op all_nodes_known_list
    (nodes : node_id fset)
    (candidates : node_id list) : bool =
  with candidates = [] => true
  with candidates = candidate :: rest =>
    candidate \in nodes /\ all_nodes_known_list nodes rest.

op all_nodes_known
    (nodes : node_id fset)
    (candidates : node_id fset) : bool =
  all_nodes_known_list nodes (elems candidates).

op all_predecessors_delivered_list
    (delivered : delivery_store)
    (recipient : principal)
    (predecessors : node_id list) : bool =
  with predecessors = [] => true
  with predecessors = predecessor :: rest =>
       delivered recipient predecessor
    /\ all_predecessors_delivered_list delivered recipient rest.

op all_predecessors_delivered
    (delivered : delivery_store)
    (recipient : principal)
    (predecessors : node_id fset) : bool =
  all_predecessors_delivered_list delivered recipient (elems predecessors).

(* ------------------------------------------------------------------------- *)
(* Complete query log and the paper's three bee-safe_kappa alternatives.       *)
(* ------------------------------------------------------------------------- *)

type live_query_kind = [
  | LiveCreateQuery of principal
  | LiveAddQuery of principal & principal
  | LiveRemoveQuery of principal & principal
  | LiveUpdateQuery of principal
  | LiveDeliverQuery of principal & principal
  | LiveRevealQuery of principal
  | LiveChallengeQuery of principal
  | LiveCompromiseQuery of principal
  | LiveHistoryOutputQuery of principal & segment_id
  | LiveHistoryCapabilityQuery of principal & segment_id
  | LiveSubmitOperationQuery of operation_id option & bool
].

type live_query = {
  lq_kind : live_query_kind;
  lq_operation : node_id option
}.

op query_kind_is_update_by
    (kind : live_query_kind)
    (member : principal) : bool =
  with kind = LiveUpdateQuery updater => updater = member
  with kind = _ => false.

op query_is_update_by
    (query : live_query)
    (member : principal) : bool =
  query_kind_is_update_by query.`lq_kind member.

op query_kind_is_challenge (kind : live_query_kind) : bool =
  with kind = LiveChallengeQuery member => true
  with kind = _ => false.

op query_is_challenge (query : live_query) : bool =
  query_kind_is_challenge query.`lq_kind.

op query_kind_is_compromise_of
    (kind : live_query_kind)
    (member : principal) : bool =
  with kind = LiveCompromiseQuery compromised => compromised = member
  with kind = _ => false.

op query_is_compromise_of
    (query : live_query)
    (member : principal) : bool =
  query_kind_is_compromise_of query.`lq_kind member.

op query_kind_challenge_member
    (kind : live_query_kind) : principal option =
  with kind = LiveChallengeQuery member => Some member
  with kind = _ => None.

op query_challenge_member (query : live_query) : principal option =
  query_kind_challenge_member query.`lq_kind.

op query_kind_compromise_member
    (kind : live_query_kind) : principal option =
  with kind = LiveCompromiseQuery member => Some member
  with kind = _ => None.

op query_compromise_member (query : live_query) : principal option =
  query_kind_compromise_member query.`lq_kind.

op count_updates_between
    (relation : causal_relation)
    (member : principal)
    (lower upper : node_id)
    (queries : live_query list) : int =
  with queries = [] => 0
  with queries = query :: rest =>
    (if query_is_update_by query member /\
        query.`lq_operation <> None /\
        causally_before relation lower (oget query.`lq_operation) /\
        causally_at_or_before relation (oget query.`lq_operation) upper
     then 1 else 0)
    + count_updates_between relation member lower upper rest.

op count_updates_at_or_before
    (relation : causal_relation)
    (member : principal)
    (upper : node_id)
    (queries : live_query list) : int =
  with queries = [] => 0
  with queries = query :: rest =>
    (if query_is_update_by query member /\
        query.`lq_operation <> None /\
        causally_at_or_before relation (oget query.`lq_operation) upper
     then 1 else 0)
    + count_updates_at_or_before relation member upper rest.

op bee_safe_pair
    (kappa : int)
    (relation : causal_relation)
    (queries : live_query list)
    (challenge compromise : live_query) : bool =
  let challenge_node = oget challenge.`lq_operation in
  let compromise_node = oget compromise.`lq_operation in
  let compromised_member = oget (query_compromise_member compromise) in
       (* kappa-forward secrecy with updates *)
       kappa <= count_updates_between
                  relation compromised_member
                  challenge_node compromise_node queries
    \/ (* post-compromise security *)
       0 < count_updates_between
             relation compromised_member
             compromise_node challenge_node queries
    \/ (* kappa-cross-fork security *)
       (kappa <= count_updates_at_or_before
                   relation compromised_member compromise_node queries
        /\ causally_concurrent relation challenge_node compromise_node).

op every_compromise_safe_for_challenge
    (kappa : int)
    (relation : causal_relation)
    (all_queries remaining : live_query list)
    (challenge : live_query) : bool =
  with remaining = [] => true
  with remaining = query :: rest =>
    (if query_compromise_member query = None
     then true
     else
          challenge.`lq_operation <> None
       /\ query.`lq_operation <> None
       /\ bee_safe_pair kappa relation all_queries challenge query)
    /\ every_compromise_safe_for_challenge
         kappa relation all_queries rest challenge.

op every_challenge_safe
    (kappa : int)
    (relation : causal_relation)
    (all_queries remaining : live_query list) : bool =
  with remaining = [] => true
  with remaining = query :: rest =>
    (if query_challenge_member query = None
     then true
     else
          query.`lq_operation <> None
       /\ every_compromise_safe_for_challenge
            kappa relation all_queries all_queries query)
    /\ every_challenge_safe kappa relation all_queries rest.

op bee_safe_kappa
    (kappa : int)
    (relation : causal_relation)
    (queries : live_query list) : bool =
     1 <= kappa
  /\ every_challenge_safe kappa relation queries queries.

op challenge_query_count (queries : live_query list) : int =
  with queries = [] => 0
  with queries = query :: rest =>
    (if query_is_challenge query then 1 else 0)
      + challenge_query_count rest.

op live_trace_admissible
    (kappa : int)
    (relation : causal_relation)
    (queries : live_query list)
    (runtime_fault : bool) : bool =
     ! runtime_fault
  /\ 0 < challenge_query_count queries
  /\ bee_safe_kappa kappa relation queries.

(* ------------------------------------------------------------------------- *)
(* Shared executable application environment.                                 *)
(* ------------------------------------------------------------------------- *)

module type LIVE_PROTOCOL_ORACLE = {
  proc sign_operation(envelope : operation_envelope) : signed_operation
  proc sign_authorization_fact(
    fact : authorization_fact
  ) : signed_authorization_fact

  proc create_group(
    creator : principal,
    initial_members : principal fset
  ) : node_id option

  proc add_member(author : principal, target : principal) : node_id option
  proc remove_member(author : principal, target : principal) : node_id option
  proc send_beekem_update(author : principal) : node_id option
  proc deliver(node : node_id, recipient : principal) : bool

  proc reveal_live_key(
    member : principal,
    node : node_id
  ) : live_application_key option

  proc challenge_live(
    member : principal,
    node : node_id
  ) : live_application_key option

  proc reveal_history_output(
    member : principal,
    node : node_id,
    segment : segment_id
  ) : history_domain_output option

  proc reveal_history_capability(
    member : principal,
    node : node_id,
    segment : segment_id,
    cover : segment_cover
  ) : history_capability_output option

  proc compromise_protocol_state(
    member : principal
  ) : beekem_snapshot option

  proc submit_operation(
    operation : signed_operation,
    view : public_view
  ) : bool
}.

op live_query_kind_of_control
    (expected_kind : beekem_control_kind)
    (expected_author : principal)
    (expected_target : principal option) : live_query_kind =
  with expected_kind = BeeCreate => LiveCreateQuery expected_author
  with expected_kind = BeeAdd =>
    LiveAddQuery expected_author (oget expected_target)
  with expected_kind = BeeRemove =>
    LiveRemoveQuery expected_author (oget expected_target)
  with expected_kind = BeeUpdate => LiveUpdateQuery expected_author.

module LiveProtocolCore(
  Auth : ORIGIN_TRACKED_UNAUTHORIZED_ORACLE,
  B : BEEKEM_LIVE_RUNTIME,
  K : MULTI_DOMAIN_KEY_SCHEDULE,
  R : LIVE_KEY_SAMPLER
) = {

  var hidden_bit : bool
  var kappa : int
  var group_created : bool
  var creator : principal
  var public_state : protocol_state
  var current_authorization_digest : authorization_digest
  var active_members : active_member_store
  var nodes : node_id fset
  var controls : control_store
  var node_digests : node_digest_store
  var delivered : delivery_store
  var member_secrets : member_secret_store
  var member_heads : member_head_store
  var relation : causal_relation
  var queries : live_query list
  var revealed_live_nodes : node_id fset
  var challenged_live_nodes : node_id fset
  var runtime_fault : bool

  proc init(
    initial_state : protocol_state,
    retention_kappa : int,
    challenge_bit : bool,
    initial_authorization_digest : authorization_digest
  ) : unit = {
    B.init();

    hidden_bit <- challenge_bit;
    kappa <- retention_kappa;
    group_created <- false;
    creator <- initial_state.`ps_creator;
    public_state <- initial_state;
    current_authorization_digest <- initial_authorization_digest;
    active_members <- empty_active_member_store;
    nodes <- fset0;
    controls <- empty_control_store;
    node_digests <- empty_node_digest_store;
    delivered <- empty_delivery_store;
    member_secrets <- empty_member_secret_store;
    member_heads <- empty_member_head_store;
    relation <- empty_causal_relation;
    queries <- [];
    revealed_live_nodes <- fset0;
    challenged_live_nodes <- fset0;
    runtime_fault <- false;
  }

  proc install_step(
    step : beekem_step_result,
    expected_kind : beekem_control_kind,
    expected_author : principal,
    expected_target : principal option
  ) : node_id option = {
    var message : beekem_control_message;
    var valid : bool;
    var node : node_id;
    var query_kind : live_query_kind;
    var installed : node_id option;

    message <- step.`bsr_message;
    node <- message.`bcm_node;
    valid <-
         message.`bcm_kind = expected_kind
      /\ message.`bcm_author = expected_author
      /\ message.`bcm_target = expected_target
      /\ message.`bcm_authorization_digest = current_authorization_digest
      /\ node \notin nodes
      /\ all_nodes_known nodes message.`bcm_predecessors
      /\ all_predecessors_delivered
           delivered expected_author message.`bcm_predecessors;
    query_kind <- LiveUpdateQuery expected_author;
    installed <- None;

    if (valid) {
      nodes <- nodes `|` fset1 node;
      controls <- control_store_put controls node message;
      node_digests <-
        node_digest_store_put
          node_digests node current_authorization_digest;
      relation <-
        causal_relation_extend relation node message.`bcm_predecessors;
      delivered <-
        delivery_store_put delivered expected_author node true;
      member_heads <-
        member_head_store_put member_heads expected_author node;
      member_secrets <-
        member_secret_store_put
          member_secrets expected_author node step.`bsr_secret;

      query_kind <-
        live_query_kind_of_control
          expected_kind expected_author expected_target;

      queries <- rcons queries
        {| lq_kind = query_kind; lq_operation = Some node |};
      installed <- Some node;
    } else {
      runtime_fault <- true;
    }

    return installed;
  }

  proc sign_operation(
    envelope : operation_envelope
  ) : signed_operation = {
    var operation : signed_operation;
    operation <@ Auth.sign_operation(envelope);
    return operation;
  }

  proc sign_authorization_fact(
    fact : authorization_fact
  ) : signed_authorization_fact = {
    var signed_fact : signed_authorization_fact;
    signed_fact <@ Auth.sign_authorization_fact(fact);
    return signed_fact;
  }

  proc create_group(
    requested_creator : principal,
    initial_members : principal fset
  ) : node_id option = {
    var step : beekem_step_result;
    var installed : node_id option;

    step <- witness;
    installed <- None;

    if (! group_created /\ requested_creator = creator /\
        requested_creator \notin initial_members) {
      step <@ B.create_group(
        requested_creator,
        initial_members,
        current_authorization_digest
      );
      installed <@
        install_step(step, BeeCreate, requested_creator, None);
      if (installed <> None) {
        group_created <- true;
        active_members <-
          active_member_store_put
            (active_member_store_of_set initial_members)
            requested_creator true;
      }
    }

    return installed;
  }

  proc add_member(
    author : principal,
    target : principal
  ) : node_id option = {
    var step : beekem_step_result;
    var installed : node_id option;

    step <- witness;
    installed <- None;

    if (group_created /\ active_members author /\
        ! active_members target /\ author <> target) {
      step <@ B.add_member(author, target, current_authorization_digest);
      installed <@ install_step(step, BeeAdd, author, Some target);
      if (installed <> None) {
        active_members <- active_member_store_put active_members target true;
      }
    }

    return installed;
  }

  proc remove_member(
    author : principal,
    target : principal
  ) : node_id option = {
    var step : beekem_step_result;
    var installed : node_id option;

    step <- witness;
    installed <- None;

    if (group_created /\ active_members author /\
        active_members target /\ author <> target) {
      step <@ B.remove_member(author, target, current_authorization_digest);
      installed <@ install_step(step, BeeRemove, author, Some target);
      if (installed <> None) {
        active_members <- active_member_store_put active_members target false;
      }
    }

    return installed;
  }

  proc send_beekem_update(author : principal) : node_id option = {
    var step : beekem_step_result;
    var installed : node_id option;

    step <- witness;
    installed <- None;

    if (group_created /\ active_members author) {
      step <@ B.send_update(author, current_authorization_digest);
      installed <@ install_step(step, BeeUpdate, author, None);
    }

    return installed;
  }

  proc deliver(node : node_id, recipient : principal) : bool = {
    var message_option : beekem_control_message option;
    var message : beekem_control_message;
    var secret : beekem_secret option;
    var accepted : bool;

    message_option <- controls node;
    message <- witness;
    secret <- None;
    accepted <- false;

    if (message_option <> None) {
      message <- oget message_option;
      if (active_members recipient /\
          ! delivered recipient node /\
          all_predecessors_delivered
            delivered recipient message.`bcm_predecessors) {
        secret <@ B.deliver(message, recipient);
        delivered <- delivery_store_put delivered recipient node true;
        member_heads <- member_head_store_put member_heads recipient node;
        member_secrets <-
          member_secret_store_put member_secrets recipient node secret;
        queries <- rcons queries
          {| lq_kind =
               LiveDeliverQuery message.`bcm_author recipient;
             lq_operation = Some node |};
        accepted <- true;
      }
    }

    return accepted;
  }

  proc reveal_live_key(
    member : principal,
    node : node_id
  ) : live_application_key option = {
    var secret_option : beekem_secret option;
    var digest_option : authorization_digest option;
    var label : live_key_label;
    var key : live_application_key;
    var result : live_application_key option;

    secret_option <- member_secrets member node;
    digest_option <- node_digests node;
    label <- witness;
    key <- witness;
    result <- None;

    if (secret_option <> None /\ digest_option <> None /\
        node \notin revealed_live_nodes /\
        node \notin challenged_live_nodes) {
      label <- live_label_of public_state node (oget digest_option);
      key <@ K.derive_live(oget secret_option, label);
      revealed_live_nodes <- revealed_live_nodes `|` fset1 node;
      queries <- rcons queries
        {| lq_kind = LiveRevealQuery member;
           lq_operation = Some node |};
      result <- Some key;
    }

    return result;
  }

  proc challenge_live(
    member : principal,
    node : node_id
  ) : live_application_key option = {
    var secret_option : beekem_secret option;
    var digest_option : authorization_digest option;
    var label : live_key_label;
    var real_key : live_application_key;
    var random_key : live_application_key;
    var response : live_application_key;
    var result : live_application_key option;

    secret_option <- member_secrets member node;
    digest_option <- node_digests node;
    label <- witness;
    real_key <- witness;
    random_key <- witness;
    response <- witness;
    result <- None;

    if (secret_option <> None /\ digest_option <> None /\
        node \notin revealed_live_nodes /\
        node \notin challenged_live_nodes) {
      label <- live_label_of public_state node (oget digest_option);
      real_key <@ K.derive_live(oget secret_option, label);
      random_key <@ R.sample(label);
      response <- if hidden_bit then real_key else random_key;
      challenged_live_nodes <- challenged_live_nodes `|` fset1 node;
      queries <- rcons queries
        {| lq_kind = LiveChallengeQuery member;
           lq_operation = Some node |};
      result <- Some response;
    }

    return result;
  }

  proc reveal_history_output(
    member : principal,
    node : node_id,
    segment : segment_id
  ) : history_domain_output option = {
    var secret_option : beekem_secret option;
    var digest_option : authorization_digest option;
    var label : history_key_label;
    var output : history_domain_output;
    var result : history_domain_output option;

    secret_option <- member_secrets member node;
    digest_option <- node_digests node;
    label <- witness;
    output <- witness;
    result <- None;

    if (secret_option <> None /\ digest_option <> None) {
      label <- history_label_of public_state segment (oget digest_option);
      output <@ K.derive_history(oget secret_option, label);
      queries <- rcons queries
        {| lq_kind = LiveHistoryOutputQuery member segment;
           lq_operation = Some node |};
      result <- Some output;
    }

    return result;
  }

  proc reveal_history_capability(
    member : principal,
    node : node_id,
    segment : segment_id,
    cover : segment_cover
  ) : history_capability_output option = {
    var secret_option : beekem_secret option;
    var digest_option : authorization_digest option;
    var label : history_key_label;
    var output : history_capability_output;
    var result : history_capability_output option;

    secret_option <- member_secrets member node;
    digest_option <- node_digests node;
    label <- witness;
    output <- witness;
    result <- None;

    if (secret_option <> None /\ digest_option <> None) {
      label <- history_label_of public_state segment (oget digest_option);
      output <@
        K.derive_history_capability(oget secret_option, label, cover);
      queries <- rcons queries
        {| lq_kind = LiveHistoryCapabilityQuery member segment;
           lq_operation = Some node |};
      result <- Some output;
    }

    return result;
  }

  proc compromise_protocol_state(
    member : principal
  ) : beekem_snapshot option = {
    var head_option : node_id option;
    var snapshot : beekem_snapshot;
    var result : beekem_snapshot option;

    head_option <- member_heads member;
    snapshot <- witness;
    result <- None;

    if (group_created /\ active_members member /\ head_option <> None) {
      snapshot <@ B.compromise(member);
      queries <- rcons queries
        {| lq_kind = LiveCompromiseQuery member;
           lq_operation = head_option |};
      result <- Some snapshot;
    }

    return result;
  }

  proc submit_operation(
    operation : signed_operation,
    view : public_view
  ) : bool = {
    var envelope_option : operation_envelope option;
    var operation_identifier : operation_id option;
    var accepted : bool;

    envelope_option <- decode_operation operation.`so_raw;
    operation_identifier <-
      if envelope_option = None
      then None
      else Some (oget envelope_option).`oe_operation_id;

    accepted <@ Auth.submit(operation, view);
    if (accepted /\ envelope_option <> None) {
      (* Production acceptance establishes equality between this signed field
         and the normalized exact causal authorization state.  The origin-aware
         validator remains the sole authority for that check. *)
      current_authorization_digest <-
        (oget envelope_option).`oe_authorization_digest;
    }

    queries <- rcons queries
      {| lq_kind =
           LiveSubmitOperationQuery operation_identifier accepted;
         lq_operation = None |};

    return accepted;
  }
}.

module type LIVE_KEY_ADVERSARY(O : LIVE_PROTOCOL_ORACLE) = {
  proc attack() : unit
  proc guess() : bool
}.

module LiveReal(
  A : LIVE_KEY_ADVERSARY,
  S : SIGNATURE_SCHEME,
  H : NODE_HASH,
  B : BEEKEM_LIVE_RUNTIME,
  K : MULTI_DOMAIN_KEY_SCHEDULE,
  R : LIVE_KEY_SAMPLER
) = {
  module SO = PG.LoggedSignatureOracle(S)
  module Auth = OriginTrackedCandidateEnvironment(SO, H)
  module O = LiveProtocolCore(Auth, B, K, R)
  module A = A(O)

  proc main(
    initial_state : protocol_state,
    initial_facts : signed_authorization_fact list,
    retention_kappa : int
  ) : bool = {
    var challenge_bit : bool;
    var adversary_guess : bool;
    var normalized_valid : bool;
    var normalized_state : authorization_state;
    var initial_digest : authorization_digest;

    normalized_valid <- false;
    normalized_state <- empty_authorization_state;
    initial_digest <- InvalidAuthorizationDigest 0;

    SO.init();
    Auth.init(initial_state);
    (normalized_valid, normalized_state) <@
      NormalizeAuthorization(Auth.Scheme).normalize(
        initial_facts,
        initial_state.`ps_creator
      );
    initial_digest <-
      if normalized_valid
      then authorization_digest_of normalized_state
      else InvalidAuthorizationDigest 0;

    challenge_bit <$ {0,1};
    O.init(
      initial_state,
      retention_kappa,
      challenge_bit,
      initial_digest
    );
    A.attack();
    adversary_guess <@ A.guess();

    return
         live_trace_admissible
           retention_kappa O.relation O.queries O.runtime_fault
      /\ adversary_guess = challenge_bit;
  }
}.

(* Fixed-bit projections execute the same origin-aware authentication oracle,
   live environment, and adversary.  Only the hidden-bit sampler is replaced
   by the procedure argument. *)
module LiveRealBit(
  A : LIVE_KEY_ADVERSARY,
  S : SIGNATURE_SCHEME,
  H : NODE_HASH,
  B : BEEKEM_LIVE_RUNTIME,
  K : MULTI_DOMAIN_KEY_SCHEDULE,
  R : LIVE_KEY_SAMPLER
) = {
  module SO = PG.LoggedSignatureOracle(S)
  module Auth = OriginTrackedCandidateEnvironment(SO, H)
  module O = LiveProtocolCore(Auth, B, K, R)
  module A = A(O)

  proc main(
    initial_state : protocol_state,
    initial_facts : signed_authorization_fact list,
    retention_kappa : int,
    challenge_bit : bool
  ) : bool = {
    var adversary_guess : bool;
    var normalized_valid : bool;
    var normalized_state : authorization_state;
    var initial_digest : authorization_digest;

    normalized_valid <- false;
    normalized_state <- empty_authorization_state;
    initial_digest <- InvalidAuthorizationDigest 0;

    SO.init();
    Auth.init(initial_state);
    (normalized_valid, normalized_state) <@
      NormalizeAuthorization(Auth.Scheme).normalize(
        initial_facts,
        initial_state.`ps_creator
      );
    initial_digest <-
      if normalized_valid
      then authorization_digest_of normalized_state
      else InvalidAuthorizationDigest 0;

    O.init(
      initial_state,
      retention_kappa,
      challenge_bit,
      initial_digest
    );
    A.attack();
    adversary_guess <@ A.guess();

    return
         live_trace_admissible
           retention_kappa O.relation O.queries O.runtime_fault
      /\ adversary_guess;
  }
}.

(* ------------------------------------------------------------------------- *)
(* Deterministic controls used only for non-vacuity and mutation witnesses.    *)
(* ------------------------------------------------------------------------- *)

op node_after (node : node_id) : node_id =
  with node = NodeId value => NodeId (value + 1).

op test_secret_for_node (node : node_id) : beekem_secret =
  with node = NodeId value => BeeKemSecret (1000 + value).

module TestBeeKemLiveRuntime : BEEKEM_LIVE_RUNTIME = {
  var next_node : node_id
  var latest_node : node_id option
  var generation : int

  proc init() : unit = {
    next_node <- NodeId 1;
    latest_node <- None;
    generation <- 0;
  }

  proc make_step(
    kind : beekem_control_kind,
    author : principal,
    target : principal option,
    digest : authorization_digest,
    carries_secret : bool
  ) : beekem_step_result = {
    var node : node_id;
    var predecessors : node_id fset;
    var secret : beekem_secret option;

    node <- next_node;
    predecessors <-
      if latest_node = None then fset0 else fset1 (oget latest_node);
    secret <-
      if carries_secret then Some (test_secret_for_node node) else None;

    next_node <- node_after next_node;
    latest_node <- Some node;
    generation <- generation + 1;

    return
      {| bsr_message =
           {| bcm_node = node;
              bcm_kind = kind;
              bcm_author = author;
              bcm_target = target;
              bcm_predecessors = predecessors;
              bcm_authorization_digest = digest |};
         bsr_secret = secret |};
  }

  proc create_group(
    creator : principal,
    initial_members : principal fset,
    digest : authorization_digest
  ) : beekem_step_result = {
    var result : beekem_step_result;
    result <@ make_step(BeeCreate, creator, None, digest, true);
    return result;
  }

  proc add_member(
    author : principal,
    target : principal,
    digest : authorization_digest
  ) : beekem_step_result = {
    var result : beekem_step_result;
    result <@ make_step(BeeAdd, author, Some target, digest, false);
    return result;
  }

  proc remove_member(
    author : principal,
    target : principal,
    digest : authorization_digest
  ) : beekem_step_result = {
    var result : beekem_step_result;
    result <@ make_step(BeeRemove, author, Some target, digest, false);
    return result;
  }

  proc send_update(
    author : principal,
    digest : authorization_digest
  ) : beekem_step_result = {
    var result : beekem_step_result;
    result <@ make_step(BeeUpdate, author, None, digest, true);
    return result;
  }

  proc deliver(
    message : beekem_control_message,
    recipient : principal
  ) : beekem_secret option = {
    return Some (test_secret_for_node message.`bcm_node);
  }

  proc compromise(principal : principal) : beekem_snapshot = {
    return {| bs_principal = principal; bs_generation = generation |};
  }
}.

op test_live_material
    (secret : beekem_secret)
    (label : live_key_label) : int =
  with secret = BeeKemSecret value =>
    value + label.`lkl_protocol_version.

op test_history_material
    (secret : beekem_secret)
    (label : history_key_label) : int =
  with secret = BeeKemSecret value =>
    value + label.`hkl_protocol_version + 10000.

module TestMultiDomainKeySchedule : MULTI_DOMAIN_KEY_SCHEDULE = {
  proc derive_live(
    secret : beekem_secret,
    label : live_key_label
  ) : live_application_key = {
    return LiveApplicationKey (test_live_material secret label) label;
  }

  proc derive_history(
    secret : beekem_secret,
    label : history_key_label
  ) : history_domain_output = {
    return HistoryDomainOutput (test_history_material secret label) label;
  }

  proc derive_history_capability(
    secret : beekem_secret,
    label : history_key_label,
    cover : segment_cover
  ) : history_capability_output = {
    return
      HistoryCapabilityOutput
        (test_history_material secret label) label cover;
  }
}.

module TestLiveKeySampler : LIVE_KEY_SAMPLER = {
  proc sample(label : live_key_label) : live_application_key = {
    return LiveApplicationKey (-1) label;
  }
}.
