require import AllCore List FSet.
require import ProtocolTypes CanonicalEncoding ProtocolPrimitives AuthorizationState.
require import ProtocolChecks ProtocolOracles.

(* The environment must classify an accepted operation from the exact
   normalization and signature-verification executions performed by the
   validator.  These contracts make the module-level evidence boundary
   explicit and prevent a later game from silently re-running either
   primitive. *)
section ExactValidatorEvidence.
  declare module S <: SIGNATURE_SCHEME.
  module V = ValidateOperation(S).

  lemma validate_decoded_acceptance_records_exact_evidence
      (input_operation : signed_operation)
      (input_envelope : operation_envelope)
      (input_view : public_view)
      (input_state : protocol_state) :
    hoare [V.validate_decoded :
         mode = Production
      /\ signed_operation = input_operation
      /\ envelope = input_envelope
      /\ view = input_view
      /\ state = input_state
      ==>
      res.`vr_accepted =>
           V.last_decoded_envelope = Some input_envelope
        /\ V.last_fact_ids = fact_ids_of_signed_facts input_view.`pv_facts
        /\ V.last_closure =
             exact_predecessor_closure
               input_state input_envelope.`oe_direct_predecessors
        /\ V.last_authorization_valid
        /\ V.last_signature_checked
        /\ V.last_signature_valid].
  proof.
    proc.
    wp.
    call (_ : true ==> true).
    wp.
    call (_ : true ==> true).
    auto=> />.
    rewrite /defense_enabled /validation_success /validation_error.
    smt().
  qed.

  lemma validate_acceptance_records_exact_evidence
      (input_operation : signed_operation)
      (input_view : public_view)
      (input_state : protocol_state) :
    hoare [V.validate :
         mode = Production
      /\ signed_operation = input_operation
      /\ view = input_view
      /\ state = input_state
      ==>
      res.`vr_accepted =>
           V.last_decoded_envelope =
             decode_operation input_operation.`so_raw
        /\ V.last_decoded_envelope <> None
        /\ V.last_fact_ids = fact_ids_of_signed_facts input_view.`pv_facts
        /\ V.last_closure =
             exact_predecessor_closure
               input_state
               (oget V.last_decoded_envelope).`oe_direct_predecessors
        /\ V.last_authorization_valid
        /\ V.last_signature_checked
        /\ V.last_signature_valid].
  proof.
    proc.
    call (validate_decoded_acceptance_records_exact_evidence
      input_operation envelope input_view input_state).
    auto=> />.
    rewrite /defense_enabled /validation_success /validation_error.
    smt().
  qed.
end section ExactValidatorEvidence.
