require import AllCore List FSet.
require import ProtocolTypes CanonicalEncoding ProtocolPrimitives AuthorizationState.
require import ProtocolChecks ProtocolOracles AuthorizationAncestry UnauthorizedReduction.

(* A5's mathematical authorization state is replayed from the exact signed
   public view with the same observed-remove transition operator used by the
   executable normalizer.  Cryptographic signature-origin failures are handled
   by the preceding A2/A3 primitive games; this predicate captures the ideal
   causal and authorization semantics after those bad events are excluded. *)
op ideal_authorization_state
    (view : public_view)
    (state : protocol_state) : authorization_state option =
  authorization_policy_replay state.`ps_creator view.`pv_facts.

pred ideal_decoded_authorized
    (operation : signed_operation)
    (envelope : operation_envelope)
    (view : public_view)
    (state : protocol_state) =
     envelope.`oe_protocol_domain = expected_protocol_domain
  /\ envelope.`oe_protocol_version = expected_protocol_version
  /\ envelope.`oe_document_id = state.`ps_document_id
  /\ envelope.`oe_operation_id \notin state.`ps_seen_operation_ids
  /\ envelope.`oe_nonce \notin state.`ps_seen_nonces
  /\ all_predecessors_exist state envelope.`oe_direct_predecessors
  /\ exact_predecessor_closure state envelope.`oe_direct_predecessors <> None
  /\ fact_ids_of_signed_facts view.`pv_facts =
       oget (exact_predecessor_closure
         state envelope.`oe_direct_predecessors)
  /\ view.`pv_observed_fact_ids =
       fact_ids_of_signed_facts view.`pv_facts
  /\ ideal_authorization_state view state <> None
  /\ envelope.`oe_authorization_digest =
       authorization_digest_of (oget (ideal_authorization_state view state))
  /\ operation.`so_signature.`sig_verification_key =
       envelope.`oe_author.`p_verification_key
  /\ member_active Production
       (oget (ideal_authorization_state view state)) envelope.`oe_author
  /\ capability_active Production
       (oget (ideal_authorization_state view state)) envelope.`oe_author
       envelope.`oe_required_capability
  /\ envelope.`oe_required_capability =
       required_capability_for_operation
         envelope.`oe_operation_kind envelope.`oe_operation_body
  /\ operation_body_valid_for_envelope envelope.

pred ideal_authorized_candidate
    (operation : signed_operation)
    (view : public_view)
    (state : protocol_state) =
     decode_operation operation.`so_raw <> None
  /\ canonical_reencoding operation.`so_raw
  /\ ideal_decoded_authorized
       operation (oget (decode_operation operation.`so_raw)) view state.

section A5ValidatorSoundness.
  declare module S <: SIGNATURE_SCHEME.

  (* The theorem follows the real production procedure.  Successful
     normalization is related to pure policy replay by the checked A3 ancestry
     contract; acceptance of every subsequent guard then establishes the exact
     ideal authorization predicate. *)
  lemma validate_decoded_acceptance_implies_ideal_authorization
      (input_operation : signed_operation)
      (input_envelope : operation_envelope)
      (input_view : public_view)
      (input_state : protocol_state) :
    hoare [ValidateOperation(S).validate_decoded :
         mode = Production
      /\ signed_operation = input_operation
      /\ envelope = input_envelope
      /\ view = input_view
      /\ state = input_state
      ==>
      res.`vr_accepted =>
        ideal_decoded_authorized
          input_operation input_envelope input_view input_state].
  proof.
    proc.
    wp.
    call (_ : true ==> true).
    wp.
    call (normalize_success_implies_policy_ancestry
      input_view.`pv_facts input_state.`ps_creator).
    auto=> />.
    rewrite /ideal_decoded_authorized /ideal_authorization_state
      /authorization_ancestry_valid /defense_enabled
      /validation_success /validation_error.
    smt().
  qed.

  (* The public validator adds decoding and canonical re-encoding before the
     decoded suffix.  Thus this is the complete A5 semantic bridge for an
     arbitrary candidate, not a theorem about a copied or weakened validator. *)
  lemma validate_acceptance_implies_ideal_authorization
      (input_operation : signed_operation)
      (input_view : public_view)
      (input_state : protocol_state) :
    hoare [ValidateOperation(S).validate :
         mode = Production
      /\ signed_operation = input_operation
      /\ view = input_view
      /\ state = input_state
      ==>
      res.`vr_accepted =>
        ideal_authorized_candidate input_operation input_view input_state].
  proof.
    proc.
    call (validate_decoded_acceptance_implies_ideal_authorization
      input_operation envelope input_view input_state).
    auto=> />.
    rewrite /ideal_authorized_candidate /defense_enabled
      /validation_success /validation_error.
    smt().
  qed.
end section A5ValidatorSoundness.

(* A5 executes the same production validator and state transition as A0.  The
   only change is the win predicate: after A1--A4 have excluded their named bad
   events, an accepted candidate is compared with the pure ideal predicate
   proved above.  The environment therefore remains reachable and accepts the
   honest witness; it is not a reject-all or constant-false game. *)
module IdealCandidateEnvironment(
  S : SIGNATURE_SCHEME,
  H : NODE_HASH
) = {
  module V = ValidateOperation(S)

  var state : protocol_state
  var accepted_operations : accepted_operation list
  var query_count : int
  var ideal_unauthorized_accepted : bool

  proc init(initial_state : protocol_state) : unit = {
    state <- initial_state;
    accepted_operations <- [];
    query_count <- 0;
    ideal_unauthorized_accepted <- false;
  }

  proc submit(
    operation : signed_operation,
    view : public_view
  ) : bool = {
    var state_before : protocol_state;
    var result : validation_result;
    var envelope : operation_envelope;
    var node : node_id;

    state_before <- state;
    result <@ V.validate(Production, operation, view, state_before);
    envelope <- witness;
    node <- witness;

    if (result.`vr_accepted) {
      envelope <- oget (decode_operation operation.`so_raw);
      node <@ H.hash(
        production_node_material envelope operation.`so_signature
      );
      state <- protocol_state_after_acceptance
        state_before envelope node view.`pv_observed_fact_ids;
      accepted_operations <- rcons accepted_operations
        {| ao_operation_id = envelope.`oe_operation_id;
           ao_author = envelope.`oe_author;
           ao_capability = envelope.`oe_required_capability;
           ao_context = view.`pv_observed_fact_ids;
           ao_transcript = production_transcript envelope |};
      ideal_unauthorized_accepted <-
        ideal_unauthorized_accepted \/
        ! ideal_authorized_candidate operation view state_before;
    }

    query_count <- query_count + 1;
    return result.`vr_accepted;
  }
}.

module UnauthorizedA5Ideal(
  A : ADAPTIVE_UNAUTHORIZED_ADVERSARY,
  S : SIGNATURE_SCHEME,
  H : NODE_HASH
) = {
  module O = IdealCandidateEnvironment(S, H)
  module A = A(O)

  proc main(initial_state : protocol_state) : bool = {
    O.init(initial_state);
    A.attack();
    return O.ideal_unauthorized_accepted;
  }
}.

section A5IdealZero.
  declare module A <: ADAPTIVE_UNAUTHORIZED_ADVERSARY.
  declare module S <: SIGNATURE_SCHEME.
  declare module H <: NODE_HASH.

  local module OI = IdealCandidateEnvironment(S, H).
  local module GI = UnauthorizedA5Ideal(A, S, H).

  lemma ideal_submit_preserves_no_unauthorized :
    hoare [OI.submit :
      ! OI.ideal_unauthorized_accepted ==>
      ! OI.ideal_unauthorized_accepted].
  proof.
    proc.
    wp.
    call (_ : true ==> true).
    call (validate_acceptance_implies_ideal_authorization
      operation view state_before).
    auto=> />.
    smt().
  qed.

  lemma ideal_main_never_unauthorized
      (initial : protocol_state) :
    hoare [GI.main :
      initial_state = initial ==> ! res].
  proof.
    proc.
    call (_ :
      ! GI.O.ideal_unauthorized_accepted).
    + exact ideal_submit_preserves_no_unauthorized.
    auto.
  qed.

  lemma ideal_unauthorized_probability_zero
      &m (initial : protocol_state) :
    Pr[
      UnauthorizedA5Ideal(A, S, H).main(initial) @ &m : res
    ] = 0%r.
  proof.
    byphoare (_ : initial_state = initial ==> ! res) => //=.
    exact (ideal_main_never_unauthorized initial).
  qed.
end section A5IdealZero.
