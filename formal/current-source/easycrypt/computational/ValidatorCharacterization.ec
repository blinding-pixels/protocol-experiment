require import AllCore List FSet.
require import ProtocolTypes CanonicalEncoding ProtocolPrimitives AuthorizationState.
require import ProtocolChecks ProtocolOracles WitnessFixtures MutationWitnesses.
require import AuthorizationWitnessTrace AuthorizationNormalizerContract.
require import HonestOperationContract.

(* A proved characterization of the real validator on the canonical seven-fact
   base state.  This operator is not a replacement validator: the theorem below
   executes [ValidateOperation(TestSignature).validate_decoded] and proves that
   its accepted bit equals this formula.  Mutation proofs may therefore reduce
   concrete game calls without copying a second procedural implementation. *)
op base_edit_decoded_accepts
    (mode : validator_mode)
    (operation : signed_operation)
    (envelope : operation_envelope) : bool =
     envelope.`oe_operation_kind = OpEdit
  /\ (! defense_enabled mode DefenseDomainVersion \/
       (envelope.`oe_protocol_domain = expected_protocol_domain /\
        envelope.`oe_protocol_version = expected_protocol_version))
  /\ (! defense_enabled mode DefenseDocumentBinding \/
       envelope.`oe_document_id = witness_base_state_exact.`ps_document_id)
  /\ (! defense_enabled mode DefenseFreshness \/
       (envelope.`oe_operation_id
          \notin witness_base_state_exact.`ps_seen_operation_ids /\
        envelope.`oe_nonce \notin witness_base_state_exact.`ps_seen_nonces))
  /\ all_predecessors_exist
       witness_base_state_exact envelope.`oe_direct_predecessors
  /\ (! defense_enabled mode DefensePredecessorCompleteness \/
       (exact_predecessor_closure
          witness_base_state_exact envelope.`oe_direct_predecessors <> None /\
        fact_ids_of_signed_facts witness_base_view_exact.`pv_facts =
          oget (exact_predecessor_closure
            witness_base_state_exact envelope.`oe_direct_predecessors)))
  /\ (! defense_enabled mode DefenseExactCausalContext \/
       witness_base_view_exact.`pv_observed_fact_ids =
         fact_ids_of_signed_facts witness_base_view_exact.`pv_facts)
  /\ (! defense_enabled mode DefenseAuthorizationDigest \/
       envelope.`oe_authorization_digest =
         authorization_digest_of witness_authorization_state_7)
  /\ (! defense_enabled mode DefenseAuthorKeyBinding \/
       operation.`so_signature.`sig_verification_key =
         envelope.`oe_author.`p_verification_key)
  /\ (! defense_enabled mode DefenseOperationSignature \/
       operation.`so_signature.`sig_bytes =
         SignatureBytes (operation_signature_message mode envelope))
  /\ member_active mode witness_authorization_state_7 envelope.`oe_author
  /\ capability_active mode witness_authorization_state_7
       envelope.`oe_author envelope.`oe_required_capability
  /\ (! defense_enabled mode DefenseRequiredCapabilityBinding \/
       envelope.`oe_required_capability =
         required_capability_for_operation
           envelope.`oe_operation_kind envelope.`oe_operation_body)
  /\ (! defense_enabled mode DefenseOperationBodyPolicy \/
       operation_body_valid_for_envelope envelope).

section BaseEditCharacterization.
  lemma base_edit_validate_decoded_characterization
      (input_mode : validator_mode)
      (input_operation : signed_operation)
      (input_envelope : operation_envelope) :
    hoare [ValidateOperation(TestSignature).validate_decoded :
         mode = input_mode
      /\ signed_operation = input_operation
      /\ envelope = input_envelope
      /\ view = witness_base_view_exact
      /\ state = witness_base_state_exact
      /\ input_envelope.`oe_operation_kind = OpEdit
      ==>
      res.`vr_accepted =
        base_edit_decoded_accepts input_mode input_operation input_envelope].
  proof.
    proc.
    inline TestSignature.verify.
    wp.
    call (normalize_witness_base_signed_facts).
    auto=> />.
    rewrite /base_edit_decoded_accepts
      witness_base_view_facts witness_base_state_creator
      /defense_enabled /validation_success /validation_error.
    smt().
  qed.

  lemma base_edit_validate_characterization
      (input_mode : validator_mode)
      (input_operation : signed_operation)
      (input_envelope : operation_envelope) :
    hoare [ValidateOperation(TestSignature).validate :
         mode = input_mode
      /\ signed_operation = input_operation
      /\ view = witness_base_view_exact
      /\ state = witness_base_state_exact
      /\ decode_operation input_operation.`so_raw = Some input_envelope
      /\ input_envelope.`oe_operation_kind = OpEdit
      ==>
      res.`vr_accepted =
        (canonical_reencoding input_operation.`so_raw \/
           ! defense_enabled input_mode DefenseCanonicalEncoding)
        /\ base_edit_decoded_accepts
             input_mode input_operation input_envelope].
  proof.
    proc.
    call (base_edit_validate_decoded_characterization
      input_mode input_operation input_envelope).
    auto=> />.
    rewrite /defense_enabled /validation_success /validation_error.
    smt().
  qed.
end section BaseEditCharacterization.
