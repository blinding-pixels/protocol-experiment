require import AllCore List FSet.
require import ProtocolTypes CanonicalEncoding PrimitiveGames AuthorizationState ProtocolChecks.

module ValidateOperation(S : SIGNATURE_SCHEME) = {
  proc validate(
    mode : validator_mode,
    signed_operation : signed_operation,
    view : public_view,
    state : protocol_state
  ) : validation_result = {
    var result : validation_result;
    var envelope_option : operation_envelope option;
    var envelope : operation_envelope;
    var fact_ids : fact_id fset;
    var closure_option : fact_id fset option;
    var authorization_valid : bool;
    var authorization : authorization_state;
    var signature_valid : bool;
    var target_option : principal option;

    result <- validation_success;
    envelope <- witness;
    fact_ids <- fset0;
    closure_option <- None;
    authorization_valid <- false;
    authorization <- empty_authorization_state;
    signature_valid <- false;
    target_option <- None;

    envelope_option <- decode_operation signed_operation.so_raw;
    if (envelope_option = None) {
      result <- validation_error FailureCanonicalDecoding;
    } else {
      envelope <- oget envelope_option;
    }

    if (result.vr_accepted /\
        defense_enabled mode DefenseCanonicalEncoding /\
        ! canonical_reencoding signed_operation.so_raw) {
      result <- validation_error FailureCanonicalReencoding;
    }

    if (result.vr_accepted /\
        defense_enabled mode DefenseDomainVersion /\
        (envelope.oe_protocol_domain <> expected_protocol_domain \/
         envelope.oe_protocol_version <> expected_protocol_version)) {
      result <- validation_error FailureDomainVersion;
    }

    if (result.vr_accepted /\
        defense_enabled mode DefenseDocumentBinding /\
        envelope.oe_document_id <> state.ps_document_id) {
      result <- validation_error FailureDocumentBinding;
    }

    if (result.vr_accepted /\
        defense_enabled mode DefenseFreshness /\
        (envelope.oe_operation_id \in state.ps_seen_operation_ids \/
         envelope.oe_nonce \in state.ps_seen_nonces)) {
      result <- validation_error FailureFreshness;
    }

    if (result.vr_accepted /\
        ! all_predecessors_exist state envelope.oe_direct_predecessors) {
      result <- validation_error FailureMissingPredecessor;
    }

    if (result.vr_accepted) {
      closure_option <-
        exact_predecessor_closure state envelope.oe_direct_predecessors;
      fact_ids <- fact_ids_of_signed_facts view.pv_facts;
    }

    if (result.vr_accepted /\
        defense_enabled mode DefensePredecessorCompleteness /\
        (closure_option = None \/ fact_ids <> oget closure_option)) {
      result <- validation_error FailurePredecessorCompleteness;
    }

    if (result.vr_accepted /\
        defense_enabled mode DefenseExactCausalContext /\
        view.pv_observed_fact_ids <> fact_ids) {
      result <- validation_error FailureExactCausalContext;
    }

    if (result.vr_accepted) {
      (authorization_valid, authorization) <@
        NormalizeAuthorization(S).normalize(view.pv_facts, state.ps_creator);
      if (! authorization_valid) {
        result <- validation_error FailureAuthorizationFacts;
      }
    }

    if (result.vr_accepted /\
        defense_enabled mode DefenseAuthorizationDigest /\
        envelope.oe_authorization_digest <>
          authorization_digest_of authorization) {
      result <- validation_error FailureAuthorizationDigest;
    }

    if (result.vr_accepted /\
        defense_enabled mode DefenseAuthorKeyBinding /\
        signed_operation.so_signature.sig_verification_key <>
          envelope.oe_author.p_verification_key) {
      result <- validation_error FailureAuthorKeyBinding;
    }

    if (result.vr_accepted /\
        defense_enabled mode DefenseOperationSignature) {
      signature_valid <@ S.verify(
        signed_operation.so_signature.sig_verification_key,
        operation_signature_message mode envelope,
        signed_operation.so_signature.sig_bytes
      );
      if (! signature_valid) {
        result <- validation_error FailureOperationSignature;
      }
    }

    if (result.vr_accepted /\
        ! member_active mode authorization envelope.oe_author) {
      result <- validation_error FailureActiveIncarnation;
    }

    if (result.vr_accepted /\
        ! capability_active mode authorization envelope.oe_author
            envelope.oe_required_capability) {
      result <- validation_error FailureRequiredCapabilityActive;
    }

    if (result.vr_accepted /\
        defense_enabled mode DefenseRequiredCapabilityBinding /\
        envelope.oe_required_capability <>
          required_capability_for_operation
            envelope.oe_operation_kind envelope.oe_operation_body) {
      result <- validation_error FailureRequiredCapabilityBinding;
    }

    if (result.vr_accepted /\
        defense_enabled mode DefenseOperationBodyPolicy /\
        ! operation_body_valid_for_envelope envelope) {
      result <- validation_error FailureOperationBodyPolicy;
    }

    if (result.vr_accepted /\ envelope.oe_operation_kind = OpAddMember) {
      target_option <- add_target_of_body envelope.oe_operation_body;
      if (target_option = None) {
        result <- validation_error FailureAddTarget;
      } else {
        if (defense_enabled mode DefenseAddTargetFreshness /\
            ! add_target_fresh authorization (oget target_option)) {
          result <- validation_error FailureAddTargetFreshness;
        }
      }
    }

    if (result.vr_accepted /\
        envelope.oe_operation_kind = OpBeeKemUpdate /\
        defense_enabled mode DefenseBeeKemPath /\
        ! beekem_update_valid state envelope) {
      result <- validation_error FailureBeeKemPath;
    }

    if (result.vr_accepted /\ envelope.oe_operation_kind = OpHistoryGrant) {
      if (state.ps_history_expectation = None) {
        result <- validation_error FailureHistoryExpectation;
      } else {
        if (history_recipient_of_body envelope.oe_operation_body = None \/
            history_merge_node_of_body envelope.oe_operation_body = None \/
            history_region_of_body envelope.oe_operation_body = None \/
            history_cover_of_body envelope.oe_operation_body = None) {
          result <- validation_error FailureHistoryEncoding;
        }
      }
    }

    if (result.vr_accepted /\ envelope.oe_operation_kind = OpHistoryGrant /\
        (oget state.ps_history_expectation).he_issuer <> envelope.oe_author) {
      result <- validation_error FailureHistoryExpectation;
    }

    if (result.vr_accepted /\ envelope.oe_operation_kind = OpHistoryGrant /\
        defense_enabled mode DefenseGrantRecipientBinding /\
        oget (history_recipient_of_body envelope.oe_operation_body) <>
          (oget state.ps_history_expectation).he_recipient) {
      result <- validation_error FailureGrantRecipientBinding;
    }

    if (result.vr_accepted /\ envelope.oe_operation_kind = OpHistoryGrant /\
        defense_enabled mode DefenseMergeNodeBinding /\
        oget (history_merge_node_of_body envelope.oe_operation_body) <>
          (oget state.ps_history_expectation).he_merge_node) {
      result <- validation_error FailureMergeNodeBinding;
    }

    if (result.vr_accepted /\ envelope.oe_operation_kind = OpHistoryGrant /\
        defense_enabled mode DefenseRegionBinding /\
        oget (history_region_of_body envelope.oe_operation_body) <>
          (oget state.ps_history_expectation).he_region) {
      result <- validation_error FailureRegionBinding;
    }

    if (result.vr_accepted /\ envelope.oe_operation_kind = OpHistoryGrant /\
        defense_enabled mode DefenseSegmentBinding /\
        (oget (history_cover_of_body envelope.oe_operation_body) <>
           (oget state.ps_history_expectation).he_cover \/
         ! cover_valid_for_region
             (oget (history_cover_of_body envelope.oe_operation_body))
             (oget (history_region_of_body envelope.oe_operation_body)))) {
      result <- validation_error FailureSegmentBinding;
    }

    if (result.vr_accepted /\ envelope.oe_operation_kind = OpPuncture /\
        ! puncture_binding_valid mode state envelope) {
      result <- validation_error FailurePuncturePolicy;
    }

    return result;
  }
}.

type protocol_query = [
  | SubmitOperationQuery of operation_id option & bool
].

module type SUBMIT_OPERATION_ORACLE = {
  proc submit(operation : signed_operation) : bool
}.

module ProtocolEnvironment(S : SIGNATURE_SCHEME, H : NODE_HASH) = {
  var mode : validator_mode
  var state : protocol_state
  var authorization_facts : signed_authorization_fact list
  var accepted_operations : accepted_operation list
  var query_log : protocol_query list
  var unauthorized_accepted : bool

  proc init(
    initial_mode : validator_mode,
    initial_state : protocol_state,
    initial_facts : signed_authorization_fact list
  ) : unit = {
    mode <- initial_mode;
    state <- initial_state;
    authorization_facts <- initial_facts;
    accepted_operations <- [];
    query_log <- [];
    unauthorized_accepted <- false;
  }

  proc submit(operation : signed_operation) : bool = {
    var envelope_option : operation_envelope option;
    var envelope : operation_envelope;
    var closure_option : fact_id fset option;
    var view : public_view;
    var result : validation_result;
    var node : node_id;
    var authorization_valid : bool;
    var authorization : authorization_state;
    var signature_valid : bool;
    var semantic_unauthorized : bool;

    envelope <- witness;
    closure_option <- None;
    view <- {| pv_facts = []; pv_observed_fact_ids = fset0 |};
    result <- validation_error FailureCanonicalDecoding;
    node <- witness;
    authorization_valid <- false;
    authorization <- empty_authorization_state;
    signature_valid <- false;
    semantic_unauthorized <- false;

    envelope_option <- decode_operation operation.so_raw;
    if (envelope_option <> None) {
      envelope <- oget envelope_option;
      closure_option <-
        exact_predecessor_closure state envelope.oe_direct_predecessors;
      if (closure_option <> None) {
        view <-
          {| pv_facts =
               signed_facts_for_ids authorization_facts (oget closure_option);
             pv_observed_fact_ids = oget closure_option |};
      }
    }

    result <@ ValidateOperation(S).validate(mode, operation, view, state);

    if (result.vr_accepted) {
      node <@ H.hash(
        production_node_material envelope operation.so_signature
      );
      state <- protocol_state_after_acceptance state envelope node
                 view.pv_observed_fact_ids;
      accepted_operations <- rcons accepted_operations
        {| ao_operation_id = envelope.oe_operation_id;
           ao_author = envelope.oe_author;
           ao_capability = envelope.oe_required_capability;
           ao_context = view.pv_observed_fact_ids;
           ao_transcript = production_transcript envelope |};

      (authorization_valid, authorization) <@
        NormalizeAuthorization(S).normalize(view.pv_facts, state.ps_creator);
      signature_valid <@ S.verify(
        operation.so_signature.sig_verification_key,
        operation_signature_message Production envelope,
        operation.so_signature.sig_bytes
      );

      semantic_unauthorized <-
           ! authorization_valid
        \/ operation.so_signature.sig_verification_key <>
             envelope.oe_author.p_verification_key
        \/ ! signature_valid
        \/ ! member_active Production authorization envelope.oe_author
        \/ ! capability_active Production authorization envelope.oe_author
             envelope.oe_required_capability
        \/ envelope.oe_required_capability <>
             required_capability_for_operation
               envelope.oe_operation_kind envelope.oe_operation_body
        \/ ! operation_body_valid_for_envelope envelope;

      unauthorized_accepted <-
        unauthorized_accepted \/ semantic_unauthorized;
    }

    query_log <- rcons query_log
      (SubmitOperationQuery
        (if envelope_option = None
         then None
         else Some envelope.oe_operation_id)
        result.vr_accepted);

    return result.vr_accepted;
  }
}.
