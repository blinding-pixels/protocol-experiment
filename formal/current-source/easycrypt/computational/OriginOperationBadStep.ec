require import AllCore List FSet.
require import ProtocolTypes CanonicalEncoding ProtocolPrimitives AuthorizationState.
require import ProtocolChecks ProtocolOracles UnauthorizedReduction UnauthorizedSignatureReduction UnauthorizedOriginGame.
require import OriginOperationVerificationEvidence OriginOperationForgeryPreservation.

import PG.

section FirstBadOperationStep.
  declare module S <: SIGNATURE_SCHEME.
  declare module H <: NODE_HASH.

  module SO = PG.LoggedSignatureOracle(S).
  module O = OriginTrackedCandidateEnvironment(SO, H).

  (* A transition from no A2 bad event to an A2 bad event can only be caused by
     the current accepted operation.  Its exact successful validator query is
     already in [SO.verify_queries], while origin failure supplies freshness
     against the unchanged signing log. *)
  lemma origin_submit_first_bad_operation_is_valid_forgery :
    hoare [O.submit :
      ! O.bad_operation_signature
      ==>
      O.bad_operation_signature =>
        PG.signature_forgery_valid
          (operation_signature_forgery_candidate
            operation (oget (decode_operation operation.`so_raw)))
          SO.sign_queries SO.verify_queries].
  proof.
    proc.
    call (candidate_submit_acceptance_logs_exact_operation_verification
      operation view state_before).
    if.
    + inline SO.get_sign_queries.
      while
        (! O.bad_operation_signature /\
         accepted /\
         decode_operation operation.`so_raw <> None /\
         envelope = oget (decode_operation operation.`so_raw) /\
         sign_queries = SO.sign_queries /\
         operation_candidate =
           operation_signature_forgery_candidate operation envelope /\
         operation.`so_signature.`sig_verification_key =
           envelope.`oe_author.`p_verification_key /\
         mem SO.verify_queries
           (operation.`so_signature.`sig_verification_key,
            operation_signature_message Production envelope,
            operation.`so_signature.`sig_bytes,
            true)).
      + auto.
      + auto=> />.
        rewrite /operation_signature_originated
          /operation_signature_forgery_candidate
          /PG.signature_forgery_valid.
        smt().
    + auto.
  qed.
end section FirstBadOperationStep.
