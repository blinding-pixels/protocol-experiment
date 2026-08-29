require import AllCore List FSet.
require import ProtocolTypes CanonicalEncoding ProtocolPrimitives AuthorizationState.
require import UnauthorizedSignatureReduction UnauthorizedOriginGame OriginOperationWitnessGame.

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

type operation_witness_bridge_result = {
  owbr_bad : bool;
  owbr_real : bool;
  owbr_win : bool
}.

(* This bridge is the named multi-user EUF-CMA experiment specialized to the
   retained-witness reduction, with the protocol bad flag and real flag merely
   returned as ghost observations.  It uses the same concrete reduction, the
   same primitive oracle, and the same single adaptive execution. *)
module OriginOperationWitnessBridgeGame(
  A : ADAPTIVE_ORIGIN_UNAUTHORIZED_ADVERSARY,
  S : SIGNATURE_SCHEME,
  H : NODE_HASH
) = {
  module SO = PG.LoggedSignatureOracle(S)
  module B = BSignOriginOperationWitness(A, H, SO)

  proc main(
    initial_state : protocol_state
  ) : operation_witness_bridge_result = {
    var forgery_option : PG.signature_forgery option;
    var forgery : PG.signature_forgery;
    var sign_queries : PG.signature_query list;
    var verify_queries : PG.signature_verification_query list;
    var win : bool;

    SO.init();
    forgery_option <@ B.forge(initial_state);
    sign_queries <@ SO.get_sign_queries();
    verify_queries <@ SO.get_verify_queries();
    forgery <- witness;
    win <- false;

    if (forgery_option <> None) {
      forgery <- oget forgery_option;
      win <- PG.signature_forgery_valid
        forgery sign_queries verify_queries;
    }

    return
      {| owbr_bad = B.O.Base.bad_operation_signature;
         owbr_real = B.O.Base.unauthorized_accepted;
         owbr_win = win |};
  }
}.

section OperationWitnessBridgeCharacterization.
  declare module A <: ADAPTIVE_ORIGIN_UNAUTHORIZED_ADVERSARY.
  declare module S <: SIGNATURE_SCHEME.
  declare module H <: NODE_HASH.

  module R = OriginOperationWitnessBridgeGame(A, S, H).

  (* The primitive win is neither a post-hoc list search nor a decorative
     advantage.  It is exactly the actual A2 bad flag, and any such flag was
     raised only by a real unauthorized acceptance. *)
  lemma operation_witness_bridge_characterization
      (initial : protocol_state) :
    hoare [R.main :
      initial_state = initial ==>
         res.`owbr_bad = res.`owbr_win
      /\ (res.`owbr_bad => res.`owbr_real)].
  proof.
    proc.
    inline R.SO.init.
    call (operation_witness_reduction_forge_characterization initial).
    inline R.SO.get_sign_queries R.SO.get_verify_queries.
    auto; rewrite /operation_forgery_witness_invariant; smt().
  qed.
end section OperationWitnessBridgeCharacterization.
