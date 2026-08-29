require import AllCore List FSet.
require import ProtocolTypes CanonicalEncoding ProtocolPrimitives AuthorizationState.
require import ProtocolChecks ProtocolOracles UnauthorizedReduction UnauthorizedSignatureReduction UnauthorizedOriginGame.

import PG.

(* A3 uses the exact authorization fact, issuer key, protocol transcript, and
   signature processed by the production normalizer. *)
op fact_signature_forgery_candidate
    (signed_fact : signed_authorization_fact) : PG.signature_forgery =
  {| sf_verification_key =
       signed_fact.`saf_signature.`sig_verification_key;
     sf_message = fact_signature_message signed_fact.`saf_fact;
     sf_signature = signed_fact.`saf_signature |}.

pred signed_fact_verification_logged
    (signed_fact : signed_authorization_fact)
    (verify_queries : PG.signature_verification_query list) =
     signed_fact.`saf_signature.`sig_verification_key =
       signed_fact.`saf_fact.`af_issuer.`p_verification_key
  /\ mem verify_queries
       (signed_fact.`saf_signature.`sig_verification_key,
        fact_signature_message signed_fact.`saf_fact,
        signed_fact.`saf_signature.`sig_bytes,
        true).

pred fact_verifications_accounted
    (facts remaining : signed_authorization_fact list)
    (verify_queries : PG.signature_verification_query list) =
  forall signed_fact,
    mem facts signed_fact =>
       mem remaining signed_fact
    \/ signed_fact_verification_logged signed_fact verify_queries.

lemma fact_verifications_accounted_initial
    (facts : signed_authorization_fact list)
    (verify_queries : PG.signature_verification_query list) :
  fact_verifications_accounted facts facts verify_queries.
proof.
  by rewrite /fact_verifications_accounted; smt().
qed.

lemma fact_verifications_accounted_complete
    (facts : signed_authorization_fact list)
    (verify_queries : PG.signature_verification_query list) :
  fact_verifications_accounted facts [] verify_queries =>
  forall signed_fact,
    mem facts signed_fact =>
    signed_fact_verification_logged signed_fact verify_queries.
proof.
  by rewrite /fact_verifications_accounted; smt().
qed.

lemma accepted_unoriginated_fact_candidate_is_forgery
    (signed_fact : signed_authorization_fact)
    (sign_queries : PG.signature_query list)
    (verify_queries : PG.signature_verification_query list) :
  signed_fact_verification_logged signed_fact verify_queries =>
  ! fact_signature_originated signed_fact sign_queries =>
  PG.signature_forgery_valid
    (fact_signature_forgery_candidate signed_fact)
    sign_queries verify_queries.
proof.
  rewrite /signed_fact_verification_logged
    /fact_signature_originated
    /fact_signature_forgery_candidate
    /PG.signature_forgery_valid.
  smt().
qed.

section ExactFactVerificationLog.
  declare module S <: SIGNATURE_SCHEME.

  module SO = PG.LoggedSignatureOracle(S).
  module Scheme = PG.SignatureOracleScheme(SO).
  module N = NormalizeAuthorization(Scheme).
  module V = ValidateOperation(Scheme).

  lemma normalize_success_logs_all_fact_verifications
      (input_facts : signed_authorization_fact list)
      (input_creator : principal) :
    hoare [N.normalize :
         facts = input_facts
      /\ creator = input_creator
      ==>
      res.`1 =>
      forall signed_fact,
        mem input_facts signed_fact =>
        signed_fact_verification_logged signed_fact SO.verify_queries].
  proof.
    proc.
    while
      (valid =>
        fact_verifications_accounted facts remaining SO.verify_queries).
    + inline Scheme.verify SO.verify.
      wp.
      call (_ : true ==> true).
      auto=> />.
      rewrite /fact_verifications_accounted
        /signed_fact_verification_logged.
      smt(head_behead).
    + auto; rewrite /fact_verifications_accounted; smt().
    + auto=> />.
      rewrite /fact_verifications_accounted
        /signed_fact_verification_logged.
      smt().
  qed.

  lemma signature_oracle_scheme_verify_preserves_fact_verification_log
      (input_facts : signed_authorization_fact list) :
    hoare [Scheme.verify :
      (forall signed_fact,
         mem input_facts signed_fact =>
         signed_fact_verification_logged signed_fact SO.verify_queries)
      ==>
      (forall signed_fact,
         mem input_facts signed_fact =>
         signed_fact_verification_logged signed_fact SO.verify_queries)].
  proof.
    proc.
    inline *.
    wp.
    call (_ : true ==> true).
    auto=> />.
    rewrite /signed_fact_verification_logged.
    smt().
  qed.

  lemma validate_decoded_acceptance_logs_all_fact_verifications
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
      forall signed_fact,
        mem input_view.`pv_facts signed_fact =>
        signed_fact_verification_logged signed_fact SO.verify_queries].
  proof.
    proc.
    wp.
    call (signature_oracle_scheme_verify_preserves_fact_verification_log
      input_view.`pv_facts).
    wp.
    call (normalize_success_logs_all_fact_verifications
      input_view.`pv_facts input_state.`ps_creator).
    auto=> />.
    rewrite /defense_enabled /validation_success /validation_error.
    smt().
  qed.

  lemma validate_acceptance_logs_all_fact_verifications
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
      forall signed_fact,
        mem input_view.`pv_facts signed_fact =>
        signed_fact_verification_logged signed_fact SO.verify_queries].
  proof.
    proc.
    call (validate_decoded_acceptance_logs_all_fact_verifications
      input_operation envelope input_view input_state).
    auto=> />.
    rewrite /defense_enabled /validation_success /validation_error.
    smt().
  qed.
end section ExactFactVerificationLog.

section CandidateSubmitFactVerificationLog.
  declare module S <: SIGNATURE_SCHEME.
  declare module H <: NODE_HASH.

  module SO = PG.LoggedSignatureOracle(S).
  module Scheme = PG.SignatureOracleScheme(SO).
  module C = CandidateUnauthorizedEnvironment(Scheme, H).

  lemma candidate_submit_acceptance_logs_all_fact_verifications
      (input_operation : signed_operation)
      (input_view : public_view)
      (input_state : protocol_state) :
    hoare [C.submit :
         operation = input_operation
      /\ view = input_view
      /\ C.state = input_state
      ==>
      res =>
      forall signed_fact,
        mem input_view.`pv_facts signed_fact =>
        signed_fact_verification_logged signed_fact SO.verify_queries].
  proof.
    proc.
    wp.
    call (_ : true ==> true).
    call (validate_acceptance_logs_all_fact_verifications
      input_operation input_view input_state).
    auto=> />.
  qed.
end section CandidateSubmitFactVerificationLog.
