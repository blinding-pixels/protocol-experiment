require import AllCore List FSet.
require import ProtocolTypes CanonicalEncoding ProtocolPrimitives AuthorizationState.
require import ProtocolChecks ProtocolOracles UnauthorizedReduction UnauthorizedSignatureReduction UnauthorizedOriginGame.
require import OriginFactVerificationEvidence OriginFactSelection.

import PG.

section FirstBadFactStep.
  declare module S <: SIGNATURE_SCHEME.
  declare module H <: NODE_HASH.

  module SO = PG.LoggedSignatureOracle(S).
  module O = OriginTrackedCandidateEnvironment(SO, H).

  (* A transition from no A3 fact-signature event to A3 bad can only be caused
     by the current accepted view.  Every fact in that view has its exact
     successful primitive verification in [SO.verify_queries], and origin
     failure selects a concrete fresh issuer/message pair from the same view. *)
  lemma origin_submit_first_bad_fact_is_valid_forgery
      (input_operation : signed_operation)
      (input_view : public_view) :
    hoare [O.submit :
         operation = input_operation
      /\ view = input_view
      /\ ! O.bad_fact_signature
      ==>
      O.bad_fact_signature =>
           O.unauthorized_accepted
        /\ first_unoriginated_fact_forgery
             input_view.`pv_facts SO.sign_queries <> None
        /\ PG.signature_forgery_valid
             (oget (first_unoriginated_fact_forgery
               input_view.`pv_facts SO.sign_queries))
             SO.sign_queries SO.verify_queries].
  proof.
    proc.
    call (candidate_submit_acceptance_logs_all_fact_verifications
      input_operation input_view state_before).
    if.
    + inline SO.get_sign_queries.
      while
        (! O.bad_fact_signature /\
         operation = input_operation /\
         view = input_view /\
         accepted /\
         sign_queries = SO.sign_queries /\
         (forall signed_fact,
            mem input_view.`pv_facts signed_fact =>
            signed_fact_verification_logged
              signed_fact SO.verify_queries)).
      + auto.
      + auto=> />.
        smt(not_all_originated_selects_valid_fact_forgery).
    + auto.
  qed.
end section FirstBadFactStep.
