require import AllCore List FSet.
require import ProtocolTypes CanonicalEncoding ProtocolPrimitives AuthorizationState.
require import ProtocolChecks ProtocolOracles AuthorizationRepresentation UnauthorizedIdeal.
require import AuthorizationLeanDeltaMapping AuthorizationLeanFullReplay.

(* A5's authorization predicate below is independent of the executable replay:
   it evaluates membership and capability in the Lean-style observed-remove fold
   defined in [AuthorizationLeanDeltaMapping].  An EasyCrypt authorization state
   appears only as a digest witness whose finite relations must represent that
   independent fold. *)
pred lean_ideal_authorization_witness
    (envelope : operation_envelope)
    (view : public_view)
    (authorization : authorization_state) =
     authorization_state_represents_lean
       authorization
       (lean_apply_signed_authorization_facts view.`pv_facts)
  /\ envelope.`oe_authorization_digest =
       authorization_digest_of authorization
  /\ lean_operation_authorized
       (lean_apply_signed_authorization_facts view.`pv_facts)
       envelope.`oe_author
       envelope.`oe_required_capability.

op lean_ideal_decoded_authorized
    (operation : signed_operation)
    (envelope : operation_envelope)
    (view : public_view)
    (state : protocol_state) : bool =
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
  /\ fact_contents_match_state state view.`pv_facts
  /\ (exists authorization,
        lean_ideal_authorization_witness envelope view authorization)
  /\ operation.`so_signature.`sig_verification_key =
       envelope.`oe_author.`p_verification_key
  /\ envelope.`oe_required_capability =
       required_capability_for_operation
         envelope.`oe_operation_kind envelope.`oe_operation_body
  /\ operation_body_valid_for_envelope envelope.

op lean_ideal_authorized_candidate
    (operation : signed_operation)
    (view : public_view)
    (state : protocol_state) : bool =
     decode_operation operation.`so_raw <> None
  /\ canonical_reencoding operation.`so_raw
  /\ lean_ideal_decoded_authorized
       operation (oget (decode_operation operation.`so_raw)) view state.

lemma represented_member_active_is_exact
    (authorization : authorization_state)
    (model : lean_observed_remove_authorization)
    (member : principal) :
  authorization_state_represents_lean authorization model =>
  (lean_member_active model member <=>
   member_active Production authorization member).
proof.
  move=> representation.
  rewrite /authorization_state_represents_lean in representation.
  rewrite /lean_member_active /member_active
    /principal_matches /defense_enabled.
  smt().
qed.

lemma represented_capability_active_is_exact
    (authorization : authorization_state)
    (model : lean_observed_remove_authorization)
    (member : principal)
    (required : capability) :
  authorization_state_represents_lean authorization model =>
  (lean_capability_active model member required <=>
   capability_active Production authorization member required).
proof.
  move=> representation.
  rewrite /authorization_state_represents_lean in representation.
  rewrite /lean_capability_active /capability_active
    /principal_matches /defense_enabled.
  smt().
qed.

lemma represented_operation_authorized_is_exact
    (authorization : authorization_state)
    (model : lean_observed_remove_authorization)
    (member : principal)
    (required : capability) :
  authorization_state_represents_lean authorization model =>
  (lean_operation_authorized model member required <=>
      member_active Production authorization member
   /\ capability_active Production authorization member required).
proof.
  move=> representation.
  rewrite /lean_operation_authorized
    (represented_member_active_is_exact
      authorization model member representation)
    (represented_capability_active_is_exact
      authorization model member required representation).
qed.

lemma ideal_decoded_authorized_implies_lean_ideal
    (operation : signed_operation)
    (envelope : operation_envelope)
    (view : public_view)
    (state : protocol_state) :
  ideal_decoded_authorized operation envelope view state =>
  lean_ideal_decoded_authorized operation envelope view state.
proof.
  move=> ideal.
  have replay_not_none :
    ideal_authorization_state view state <> None.
  + by rewrite /ideal_decoded_authorized in ideal; smt().
  have replay_some := authorization_state_option_some_oget
    (ideal_authorization_state view state) replay_not_none.
  have replay_raw := replay_some.
  rewrite /ideal_authorization_state in replay_raw.
  have representation :=
    authorization_policy_replay_matches_independent_lean_apply
      state.`ps_creator
      view.`pv_facts
      (oget (ideal_authorization_state view state))
      replay_raw.
  have lean_authorized :
    lean_operation_authorized
      (lean_apply_signed_authorization_facts view.`pv_facts)
      envelope.`oe_author
      envelope.`oe_required_capability.
  + rewrite (represented_operation_authorized_is_exact
      (oget (ideal_authorization_state view state))
      (lean_apply_signed_authorization_facts view.`pv_facts)
      envelope.`oe_author
      envelope.`oe_required_capability
      representation).
    rewrite /ideal_decoded_authorized in ideal.
    smt().
  have witness_exists :
    exists authorization,
      lean_ideal_authorization_witness envelope view authorization.
  + exists (oget (ideal_authorization_state view state)).
    rewrite /lean_ideal_authorization_witness.
    rewrite /ideal_decoded_authorized in ideal.
    smt().
  rewrite /lean_ideal_decoded_authorized.
  rewrite /ideal_decoded_authorized in ideal.
  smt(witness_exists).
qed.

lemma ideal_authorized_candidate_implies_lean_ideal
    (operation : signed_operation)
    (view : public_view)
    (state : protocol_state) :
  ideal_authorized_candidate operation view state =>
  lean_ideal_authorized_candidate operation view state.
proof.
  move=> ideal.
  rewrite /ideal_authorized_candidate in ideal.
  rewrite /lean_ideal_authorized_candidate.
  have decoded_ideal :=
    ideal_decoded_authorized_implies_lean_ideal
      operation
      (oget (decode_operation operation.`so_raw))
      view state
      ideal.`3.
  smt().
qed.
