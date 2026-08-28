require import AllCore List FSet.
require import ProtocolTypes CanonicalEncoding ProtocolPrimitives AuthorizationState.
require import ProtocolChecks ProtocolOracles UnauthorizedGame HonestOperationContract.
require import AuthorizationWitnessTrace.

(* The unauthorized-operation event is computed only from values produced by
   the production path: [authorization_valid] is returned by the concrete
   normalizer and [signature_valid] is returned by verification of the exact
   production transcript.  The adversary never supplies either Boolean. *)
op unauthorized_acceptance_condition
    (operation : signed_operation)
    (envelope : operation_envelope)
    (authorization_valid : bool)
    (authorization : authorization_state)
    (signature_valid : bool) : bool =
     ! authorization_valid
  \/ operation.`so_signature.`sig_verification_key <>
       envelope.`oe_author.`p_verification_key
  \/ ! signature_valid
  \/ ! member_active Production authorization envelope.`oe_author
  \/ ! capability_active Production authorization envelope.`oe_author
       envelope.`oe_required_capability
  \/ envelope.`oe_required_capability <>
       required_capability_for_operation
         envelope.`oe_operation_kind envelope.`oe_operation_body
  \/ ! operation_body_valid_for_envelope envelope.

lemma authorized_checks_exclude_unauthorized
    (operation : signed_operation)
    (envelope : operation_envelope)
    (authorization : authorization_state) :
     operation.`so_signature.`sig_verification_key =
       envelope.`oe_author.`p_verification_key
  => member_active Production authorization envelope.`oe_author
  => capability_active Production authorization envelope.`oe_author
       envelope.`oe_required_capability
  => envelope.`oe_required_capability =
       required_capability_for_operation
         envelope.`oe_operation_kind envelope.`oe_operation_body
  => operation_body_valid_for_envelope envelope
  => ! unauthorized_acceptance_condition
       operation envelope true authorization true.
proof.
  by rewrite /unauthorized_acceptance_condition; smt().
qed.

(* Deliverable A0 candidate interface.  This gives the adversary the complete
   public validator input: arbitrary operation bytes/signatures and an
   arbitrary public view containing signed grants, revocations, malformed fact
   signatures, and a claimed observed context.  The game owns the protocol
   state, calls the shared production validator, and computes the win event. *)
type unauthorized_candidate_query = [
  | SubmitUnauthorizedCandidateQuery of operation_id option
      & fact_id fset & bool
].

module type UNAUTHORIZED_CANDIDATE_ORACLE = {
  proc submit(
    operation : signed_operation,
    view : public_view
  ) : bool
}.

module CandidateUnauthorizedEnvironment(
  S : SIGNATURE_SCHEME,
  H : NODE_HASH
) = {
  var state : protocol_state
  var accepted_operations : accepted_operation list
  var query_log : unauthorized_candidate_query list
  var unauthorized_accepted : bool

  proc init(initial_state : protocol_state) : unit = {
    state <- initial_state;
    accepted_operations <- [];
    query_log <- [];
    unauthorized_accepted <- false;
  }

  proc submit(
    operation : signed_operation,
    view : public_view
  ) : bool = {
    var envelope_option : operation_envelope option;
    var envelope : operation_envelope;
    var result : validation_result;
    var authorization_valid : bool;
    var authorization : authorization_state;
    var signature_valid : bool;
    var semantic_unauthorized : bool;
    var node : node_id;

    envelope_option <- decode_operation operation.`so_raw;
    envelope <- witness;
    result <- validation_error FailureCanonicalDecoding;
    authorization_valid <- false;
    authorization <- empty_authorization_state;
    signature_valid <- false;
    semantic_unauthorized <- false;
    node <- witness;

    if (envelope_option <> None) {
      envelope <- oget envelope_option;
    }

    result <@ ValidateOperation(S).validate(
      Production,
      operation,
      view,
      state
    );

    if (result.`vr_accepted) {
      (authorization_valid, authorization) <@
        NormalizeAuthorization(S).normalize(
          view.`pv_facts,
          state.`ps_creator
        );
      signature_valid <@ S.verify(
        operation.`so_signature.`sig_verification_key,
        operation_signature_message Production envelope,
        operation.`so_signature.`sig_bytes
      );
      semantic_unauthorized <-
        unauthorized_acceptance_condition
          operation envelope authorization_valid authorization signature_valid;

      node <@ H.hash(
        production_node_material envelope operation.`so_signature
      );
      state <- protocol_state_after_acceptance
        state envelope node view.`pv_observed_fact_ids;
      accepted_operations <- rcons accepted_operations
        {| ao_operation_id = envelope.`oe_operation_id;
           ao_author = envelope.`oe_author;
           ao_capability = envelope.`oe_required_capability;
           ao_context = view.`pv_observed_fact_ids;
           ao_transcript = production_transcript envelope |};
      unauthorized_accepted <-
        unauthorized_accepted \/ semantic_unauthorized;
    }

    query_log <- rcons query_log
      (SubmitUnauthorizedCandidateQuery
        (if envelope_option = None
         then None
         else Some envelope.`oe_operation_id)
        view.`pv_observed_fact_ids
        result.`vr_accepted);

    return result.`vr_accepted;
  }
}.

module type ADAPTIVE_UNAUTHORIZED_ADVERSARY(
  O : UNAUTHORIZED_CANDIDATE_ORACLE
) = {
  proc attack() : unit
}.

module UnauthorizedA0Real(
  A : ADAPTIVE_UNAUTHORIZED_ADVERSARY,
  S : SIGNATURE_SCHEME,
  H : NODE_HASH
) = {
  module O = CandidateUnauthorizedEnvironment(S, H)
  module A = A(O)

  proc main(initial_state : protocol_state) : bool = {
    O.init(initial_state);
    A.attack();
    return O.unauthorized_accepted;
  }
}.

(* A0 semantic control: the concrete honest operation is not classified as an
   unauthorized acceptance.  This reuses the exact-incarnation membership,
   capability, transcript-key, capability-binding, and body-policy facts that
   discharge the production acceptance theorem. *)
lemma witness_honest_not_unauthorized :
  ! unauthorized_acceptance_condition
      witness_honest_edit_operation
      witness_honest_edit_envelope
      true
      witness_authorization_state_7
      true.
proof.
  apply (authorized_checks_exclude_unauthorized
    witness_honest_edit_operation
    witness_honest_edit_envelope
    witness_authorization_state_7).
  + exact witness_honest_author_key_binding.
  + rewrite witness_honest_author.
    exact witness_bob_old_member_active_state_7.
  + rewrite witness_honest_author
      witness_honest_required_capability_field.
    exact witness_bob_old_edit_active_state_7.
  + rewrite witness_honest_required_capability_field.
    exact witness_honest_required_capability.
  + exact witness_honest_operation_body_valid.
qed.
