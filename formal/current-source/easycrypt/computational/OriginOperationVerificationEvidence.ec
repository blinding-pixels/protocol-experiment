require import AllCore List FSet.
require import ProtocolTypes CanonicalEncoding ProtocolPrimitives AuthorizationState.
require import ProtocolChecks ProtocolOracles UnauthorizedReduction UnauthorizedSignatureReduction.

import PG.

(* The candidate used by A2 is built from the exact operation, transcript, and
   signature that reached the production validator. *)
op operation_signature_forgery_candidate
    (operation : signed_operation)
    (envelope : operation_envelope) : PG.signature_forgery =
  {| sf_verification_key = operation.`so_signature.`sig_verification_key;
     sf_message = operation_signature_message Production envelope;
     sf_signature = operation.`so_signature |}.

lemma accepted_unoriginated_operation_candidate_is_forgery
    (operation : signed_operation)
    (envelope : operation_envelope)
    (sign_queries : PG.signature_query list)
    (verify_queries : PG.signature_verification_query list) :
  operation.`so_signature.`sig_verification_key =
    envelope.`oe_author.`p_verification_key =>
  mem verify_queries
    (operation.`so_signature.`sig_verification_key,
     operation_signature_message Production envelope,
     operation.`so_signature.`sig_bytes,
     true) =>
  ! operation_signature_originated operation envelope sign_queries =>
  PG.signature_forgery_valid
    (operation_signature_forgery_candidate operation envelope)
    sign_queries verify_queries.
proof.
  rewrite /operation_signature_forgery_candidate
    /operation_signature_originated /PG.signature_forgery_valid.
  smt().
qed.

section ExactOperationVerificationLog.
  declare module S <: SIGNATURE_SCHEME.

  module SO = PG.LoggedSignatureOracle(S).
  module Scheme = PG.SignatureOracleScheme(SO).
  module V = ValidateOperation(Scheme).

  lemma signature_oracle_scheme_verify_records_exact_query
      (input_vk : verification_key)
      (input_message : signature_message)
      (input_bytes : signature_bytes) :
    hoare [Scheme.verify :
         vk = input_vk
      /\ message = input_message
      /\ bytes = input_bytes
      ==>
      mem SO.verify_queries
        (input_vk, input_message, input_bytes, res)].
  proof.
    proc.
    inline *.
    wp.
    call (_ : true ==> true).
    auto.
  qed.

  lemma validate_decoded_acceptance_logs_exact_operation_verification
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
           input_operation.`so_signature.`sig_verification_key =
             input_envelope.`oe_author.`p_verification_key
        /\ mem SO.verify_queries
             (input_operation.`so_signature.`sig_verification_key,
              operation_signature_message Production input_envelope,
              input_operation.`so_signature.`sig_bytes,
              true)].
  proof.
    proc.
    wp.
    call (signature_oracle_scheme_verify_records_exact_query
      input_operation.`so_signature.`sig_verification_key
      (operation_signature_message Production input_envelope)
      input_operation.`so_signature.`sig_bytes).
    wp.
    call (_ : true ==> true).
    auto=> />.
    rewrite /defense_enabled /validation_success /validation_error.
    smt().
  qed.

  lemma validate_acceptance_logs_exact_operation_verification
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
           decode_operation input_operation.`so_raw <> None
        /\ input_operation.`so_signature.`sig_verification_key =
             (oget (decode_operation input_operation.`so_raw)).`oe_author.`p_verification_key
        /\ mem SO.verify_queries
             (input_operation.`so_signature.`sig_verification_key,
              operation_signature_message Production
                (oget (decode_operation input_operation.`so_raw)),
              input_operation.`so_signature.`sig_bytes,
              true)].
  proof.
    proc.
    call (validate_decoded_acceptance_logs_exact_operation_verification
      input_operation envelope input_view input_state).
    auto=> />.
    rewrite /defense_enabled /validation_success /validation_error.
    smt().
  qed.
end section ExactOperationVerificationLog.

section CandidateSubmitOperationVerificationLog.
  declare module S <: SIGNATURE_SCHEME.
  declare module H <: NODE_HASH.

  module SO = PG.LoggedSignatureOracle(S).
  module Scheme = PG.SignatureOracleScheme(SO).
  module C = CandidateUnauthorizedEnvironment(Scheme, H).

  lemma candidate_submit_acceptance_logs_exact_operation_verification
      (input_operation : signed_operation)
      (input_view : public_view)
      (input_state : protocol_state) :
    hoare [C.submit :
         operation = input_operation
      /\ view = input_view
      /\ C.state = input_state
      ==>
      res =>
           decode_operation input_operation.`so_raw <> None
        /\ input_operation.`so_signature.`sig_verification_key =
             (oget (decode_operation input_operation.`so_raw)).`oe_author.`p_verification_key
        /\ mem SO.verify_queries
             (input_operation.`so_signature.`sig_verification_key,
              operation_signature_message Production
                (oget (decode_operation input_operation.`so_raw)),
              input_operation.`so_signature.`sig_bytes,
              true)].
  proof.
    proc.
    wp.
    call (_ : true ==> true).
    call (validate_acceptance_logs_exact_operation_verification
      input_operation input_view input_state).
    auto=> />.
  qed.
end section CandidateSubmitOperationVerificationLog.
