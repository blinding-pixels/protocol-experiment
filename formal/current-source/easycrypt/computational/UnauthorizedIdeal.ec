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
  lemma validate_decoded_acceptance_implies_ideal_authorization :
    hoare [ValidateOperation(S).validate_decoded :
      mode = Production ==>
      res.`vr_accepted =>
        ideal_decoded_authorized signed_operation envelope view state].
  proof.
    proc.
    wp.
    call (_ : true ==> true).
    wp.
    call (normalize_success_implies_policy_ancestry
      view.`pv_facts state.`ps_creator).
    auto=> />.
    rewrite /ideal_decoded_authorized /ideal_authorization_state
      /authorization_ancestry_valid /defense_enabled
      /validation_success /validation_error.
    smt().
  qed.

  (* The public validator adds decoding and canonical re-encoding before the
     decoded suffix.  Thus this is the complete A5 semantic bridge for an
     arbitrary candidate, not a theorem about a copied or weakened validator. *)
  lemma validate_acceptance_implies_ideal_authorization :
    hoare [ValidateOperation(S).validate :
      mode = Production ==>
      res.`vr_accepted =>
        ideal_authorized_candidate signed_operation view state].
  proof.
    proc.
    call (validate_decoded_acceptance_implies_ideal_authorization).
    auto=> />.
    rewrite /ideal_authorized_candidate /defense_enabled
      /validation_success /validation_error.
    smt().
  qed.
end section A5ValidatorSoundness.
