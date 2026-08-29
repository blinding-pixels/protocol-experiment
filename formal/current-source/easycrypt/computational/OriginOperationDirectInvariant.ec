require import AllCore List FSet.
require import ProtocolTypes CanonicalEncoding ProtocolPrimitives AuthorizationState.
require import ProtocolChecks ProtocolOracles UnauthorizedReduction UnauthorizedSignatureReduction UnauthorizedOriginGame.
require import OriginOperationVerificationEvidence OriginOperationForgeryPreservation OriginOperationWitnessGame.

import PG.

section DirectOperationWitnessEnvironment.
  declare module S <: SIGNATURE_SCHEME.
  declare module H <: NODE_HASH.

  module SO = PG.LoggedSignatureOracle(S).
  module O = OriginTrackedCandidateEnvironment(SO, H).

  lemma origin_direct_init_establishes_operation_witness
      (initial : protocol_state) :
    hoare [O.init :
      initial_state = initial ==>
      operation_forgery_witness_invariant
        O.unauthorized_accepted
        O.bad_operation_signature
        O.operation_forgery
        SO.sign_queries SO.verify_queries].
  proof.
    rewrite /operation_forgery_witness_invariant.
    proc.
    inline *.
    auto.
  qed.

  lemma origin_direct_sign_operation_preserves_operation_witness :
    hoare [O.sign_operation :
      operation_forgery_witness_invariant
        O.unauthorized_accepted
        O.bad_operation_signature
        O.operation_forgery
        SO.sign_queries SO.verify_queries
      ==>
      operation_forgery_witness_invariant
        O.unauthorized_accepted
        O.bad_operation_signature
        O.operation_forgery
        SO.sign_queries SO.verify_queries].
  proof.
    rewrite /operation_forgery_witness_invariant.
    proc.
    if.
    + call (_ : true ==> true).
      auto.
    + auto.
  qed.

  lemma origin_direct_sign_fact_preserves_operation_witness :
    hoare [O.sign_authorization_fact :
      operation_forgery_witness_invariant
        O.unauthorized_accepted
        O.bad_operation_signature
        O.operation_forgery
        SO.sign_queries SO.verify_queries
      ==>
      operation_forgery_witness_invariant
        O.unauthorized_accepted
        O.bad_operation_signature
        O.operation_forgery
        SO.sign_queries SO.verify_queries].
  proof.
    rewrite /operation_forgery_witness_invariant.
    proc.
    if.
    + call (_ : true ==> true).
      auto.
    + auto.
  qed.

  (* Once A2 is bad, the actual origin environment keeps the exact retained
     witness unchanged.  Submit can append verification queries but cannot add
     a signing query, so the primitive forgery remains valid. *)
  lemma origin_direct_submit_preserves_existing_operation_witness
      (candidate : PG.signature_forgery) :
    hoare [O.submit :
         O.bad_operation_signature
      /\ O.unauthorized_accepted
      /\ O.operation_forgery = Some candidate
      /\ PG.signature_forgery_valid
           candidate SO.sign_queries SO.verify_queries
      ==>
         O.bad_operation_signature
      /\ O.unauthorized_accepted
      /\ O.operation_forgery = Some candidate
      /\ PG.signature_forgery_valid
           candidate SO.sign_queries SO.verify_queries].
  proof.
    proc.
    call (candidate_submit_preserves_existing_forgery candidate).
    if.
    + inline SO.get_sign_queries.
      while
        (O.bad_operation_signature /\
         O.unauthorized_accepted /\
         O.operation_forgery = Some candidate /\
         PG.signature_forgery_valid
           candidate SO.sign_queries SO.verify_queries).
      * auto.
      * auto.
    + auto.
  qed.

  (* Starting from no A2 bad event and no retained witness, one actual submit
     establishes the exact bad/witness equivalence.  If this submit is the
     first bad step, the stored value is the exact operation candidate whose
     successful production verification is already in the primitive log. *)
  lemma origin_direct_submit_from_clean_establishes_operation_witness
      (input_operation : signed_operation)
      (input_view : public_view) :
    hoare [O.submit :
         operation = input_operation
      /\ view = input_view
      /\ ! O.bad_operation_signature
      /\ O.operation_forgery = None
      ==>
      operation_forgery_witness_invariant
        O.unauthorized_accepted
        O.bad_operation_signature
        O.operation_forgery
        SO.sign_queries SO.verify_queries].
  proof.
    rewrite /operation_forgery_witness_invariant.
    proc.
    call (candidate_submit_acceptance_logs_exact_operation_verification
      input_operation input_view state_before).
    if.
    + inline SO.get_sign_queries.
      while
        (! O.bad_operation_signature /\
         O.operation_forgery = None /\
         operation = input_operation /\
         view = input_view /\
         accepted /\
         decode_operation input_operation.`so_raw <> None /\
         envelope = oget (decode_operation input_operation.`so_raw) /\
         sign_queries = SO.sign_queries /\
         operation_candidate =
           operation_signature_forgery_candidate input_operation envelope /\
         input_operation.`so_signature.`sig_verification_key =
           envelope.`oe_author.`p_verification_key /\
         mem SO.verify_queries
           (input_operation.`so_signature.`sig_verification_key,
            operation_signature_message Production envelope,
            input_operation.`so_signature.`sig_bytes,
            true)).
      + auto.
      + auto=> />.
        rewrite /operation_signature_originated
          /operation_signature_forgery_candidate
          /PG.signature_forgery_valid.
        smt().
    + auto.
  qed.
end section DirectOperationWitnessEnvironment.
