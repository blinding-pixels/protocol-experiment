require import AllCore List FSet.
require import ProtocolTypes CanonicalEncoding AuthorizationState AuthorizationRepresentation.
require import UnauthorizedIdeal UnauthorizedLeanIdeal.
require import AuthorizationLeanDeltaMapping AuthorizationLeanFullReplay.

(* Policy validity remains part of A5: facts must replay through the same
   issuer/context checks used by the validator.  The additional certificate is
   independent and load-bearing: the replay result must represent the separate
   Lean-style observed-remove fold over those exact immutable facts. *)
pred lean_replay_authorization_certificate
    (view : public_view)
    (state : protocol_state) =
  exists authorization,
       ideal_authorization_state view state = Some authorization
    /\ authorization_state_represents_lean
         authorization
         (lean_apply_signed_authorization_facts view.`pv_facts).

op lean_certified_ideal_decoded_authorized
    (operation : signed_operation)
    (envelope : operation_envelope)
    (view : public_view)
    (state : protocol_state) : bool =
     ideal_decoded_authorized operation envelope view state
  /\ lean_replay_authorization_certificate view state.

op lean_certified_ideal_authorized_candidate
    (operation : signed_operation)
    (view : public_view)
    (state : protocol_state) : bool =
     decode_operation operation.`so_raw <> None
  /\ canonical_reencoding operation.`so_raw
  /\ lean_certified_ideal_decoded_authorized
       operation (oget (decode_operation operation.`so_raw)) view state.

lemma ideal_decoded_authorized_implies_lean_replay_certificate
    (operation : signed_operation)
    (envelope : operation_envelope)
    (view : public_view)
    (state : protocol_state) :
  ideal_decoded_authorized operation envelope view state =>
  lean_replay_authorization_certificate view state.
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
  rewrite /lean_replay_authorization_certificate.
  exists (oget (ideal_authorization_state view state)).
  split.
  + exact replay_some.
  + exact representation.
qed.

lemma ideal_decoded_authorized_implies_lean_certified
    (operation : signed_operation)
    (envelope : operation_envelope)
    (view : public_view)
    (state : protocol_state) :
  ideal_decoded_authorized operation envelope view state =>
  lean_certified_ideal_decoded_authorized
    operation envelope view state.
proof.
  move=> ideal.
  rewrite /lean_certified_ideal_decoded_authorized.
  split.
  + exact ideal.
  + exact (ideal_decoded_authorized_implies_lean_replay_certificate
      operation envelope view state ideal).
qed.

lemma lean_certified_ideal_decoded_authorized_implies_ideal
    (operation : signed_operation)
    (envelope : operation_envelope)
    (view : public_view)
    (state : protocol_state) :
  lean_certified_ideal_decoded_authorized
    operation envelope view state =>
  ideal_decoded_authorized operation envelope view state.
proof. by rewrite /lean_certified_ideal_decoded_authorized; smt(). qed.

lemma lean_certified_ideal_decoded_authorized_iff
    (operation : signed_operation)
    (envelope : operation_envelope)
    (view : public_view)
    (state : protocol_state) :
  lean_certified_ideal_decoded_authorized
    operation envelope view state <=>
  ideal_decoded_authorized operation envelope view state.
proof.
  split.
  + exact (lean_certified_ideal_decoded_authorized_implies_ideal
      operation envelope view state).
  + exact (ideal_decoded_authorized_implies_lean_certified
      operation envelope view state).
qed.

lemma ideal_authorized_candidate_implies_lean_certified
    (operation : signed_operation)
    (view : public_view)
    (state : protocol_state) :
  ideal_authorized_candidate operation view state =>
  lean_certified_ideal_authorized_candidate operation view state.
proof.
  move=> ideal.
  rewrite /ideal_authorized_candidate in ideal.
  have certified := ideal_decoded_authorized_implies_lean_certified
    operation
    (oget (decode_operation operation.`so_raw))
    view state ideal.`3.
  rewrite /lean_certified_ideal_authorized_candidate.
  smt().
qed.

lemma lean_certified_ideal_authorized_candidate_implies_ideal
    (operation : signed_operation)
    (view : public_view)
    (state : protocol_state) :
  lean_certified_ideal_authorized_candidate operation view state =>
  ideal_authorized_candidate operation view state.
proof.
  move=> certified.
  rewrite /lean_certified_ideal_authorized_candidate in certified.
  have ideal_decoded :=
    lean_certified_ideal_decoded_authorized_implies_ideal
      operation
      (oget (decode_operation operation.`so_raw))
      view state certified.`3.
  rewrite /ideal_authorized_candidate.
  smt().
qed.

lemma lean_certified_ideal_authorized_candidate_iff
    (operation : signed_operation)
    (view : public_view)
    (state : protocol_state) :
  lean_certified_ideal_authorized_candidate operation view state <=>
  ideal_authorized_candidate operation view state.
proof.
  split.
  + exact (lean_certified_ideal_authorized_candidate_implies_ideal
      operation view state).
  + exact (ideal_authorized_candidate_implies_lean_certified
      operation view state).
qed.
