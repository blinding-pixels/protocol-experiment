require import AllCore List FSet.
require import ProtocolTypes CanonicalEncoding ProtocolPrimitives AuthorizationState.
require import UnauthorizedOriginGame OriginOperationWitnessGame.

import PG.

section OperationWitnessReductionAdversary.
  declare module A <: ADAPTIVE_ORIGIN_UNAUTHORIZED_ADVERSARY.
  declare module S <: SIGNATURE_SCHEME.
  declare module H <: NODE_HASH.

  module SOR = PG.LoggedSignatureOracle(S).
  module B = BSignOriginOperationWitness(A, H, SOR).

  (* The reduction is characterized before the primitive-game functor seals
     it to [MULTI_USER_EUFCMA_ADVERSARY].  Its public result is the retained
     first operation forgery from the exact adaptive A2 execution, and the
     invariant is stated against the primitive oracle's actual final logs. *)
  lemma operation_witness_reduction_forge_characterization
      (initial : protocol_state) :
    hoare [B.forge :
      initial_state = initial ==>
      operation_forgery_witness_invariant
        B.O.Base.unauthorized_accepted
        B.O.Base.bad_operation_signature
        res
        SOR.sign_queries SOR.verify_queries].
  proof.
    proc.
    call (_ :
      operation_forgery_witness_invariant
        B.O.Base.unauthorized_accepted
        B.O.Base.bad_operation_signature
        B.O.operation_forgery
        SOR.sign_queries SOR.verify_queries).
    + exact operation_witness_sign_operation_preserves_invariant.
    + exact operation_witness_sign_fact_preserves_invariant.
    + move=> input_operation input_view.
      exact (operation_witness_submit_preserves_invariant
        input_operation input_view).
    inline B.O.init B.O.Base.init B.O.Base.Base.init.
    auto; rewrite /operation_forgery_witness_invariant.
  qed.
end section OperationWitnessReductionAdversary.
