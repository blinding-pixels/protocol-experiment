require import AllCore List FSet.
require import ProtocolTypes ProtocolPrimitives UnauthorizedSignatureReduction.
require import UnauthorizedOriginPartition OriginOperationDirectInvariant.

import PG.

section DirectOperationReductionAdversary.
  declare module A <: ADAPTIVE_ORIGIN_UNAUTHORIZED_ADVERSARY.
  declare module S <: SIGNATURE_SCHEME.
  declare module H <: NODE_HASH.

  module SOR = PG.LoggedSignatureOracle(S).
  module B = BSignOriginOperationDirect(A, H, SOR).

  (* The direct reduction returns the first operation forgery retained by the
     exact A0 environment.  The invariant is stated against the primitive
     oracle's actual final sign and verification logs. *)
  lemma origin_direct_reduction_forge_characterization
      (initial : protocol_state) :
    hoare [B.forge :
      initial_state = initial ==>
      operation_forgery_witness_invariant
        B.O.unauthorized_accepted
        B.O.bad_operation_signature
        res
        SOR.sign_queries SOR.verify_queries].
  proof.
    proc.
    call (_ :
      operation_forgery_witness_invariant
        B.O.unauthorized_accepted
        B.O.bad_operation_signature
        B.O.operation_forgery
        SOR.sign_queries SOR.verify_queries).
    + exact origin_direct_sign_operation_preserves_operation_witness.
    + exact origin_direct_sign_fact_preserves_operation_witness.
    + move=> input_operation input_view.
      exact (origin_direct_submit_preserves_operation_witness
        input_operation input_view).
    inline B.O.init B.O.Base.init B.O.Base.Base.init.
    auto; rewrite /operation_forgery_witness_invariant.
  qed.
end section DirectOperationReductionAdversary.

type origin_direct_operation_bridge_result = {
  odobr_bad : bool;
  odobr_real : bool;
  odobr_win : bool
}.

(* This is the named multi-user EUF-CMA experiment specialized to the direct
   retained-witness reduction, with the protocol bad and real flags returned
   only as ghost observations.  There is one adaptive execution and one
   primitive transcript. *)
module OriginOperationDirectBridgeGame(
  A : ADAPTIVE_ORIGIN_UNAUTHORIZED_ADVERSARY,
  S : SIGNATURE_SCHEME,
  H : NODE_HASH
) = {
  module SO = PG.LoggedSignatureOracle(S)
  module B = BSignOriginOperationDirect(A, H, SO)

  proc main(
    initial_state : protocol_state
  ) : origin_direct_operation_bridge_result = {
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
      {| odobr_bad = B.O.bad_operation_signature;
         odobr_real = B.O.unauthorized_accepted;
         odobr_win = win |};
  }
}.

section DirectOperationBridgeCharacterization.
  declare module A <: ADAPTIVE_ORIGIN_UNAUTHORIZED_ADVERSARY.
  declare module S <: SIGNATURE_SCHEME.
  declare module H <: NODE_HASH.

  module R = OriginOperationDirectBridgeGame(A, S, H).

  (* A2's actual protocol bad flag is exactly the named primitive-game success
     predicate.  A bad event also implies that A0's real event occurred. *)
  lemma origin_direct_bridge_characterization
      (initial : protocol_state) :
    hoare [R.main :
      initial_state = initial ==>
         res.`odobr_bad = res.`odobr_win
      /\ (res.`odobr_bad => res.`odobr_real)].
  proof.
    proc.
    inline R.SO.init.
    call (origin_direct_reduction_forge_characterization initial).
    inline R.SO.get_sign_queries R.SO.get_verify_queries.
    auto; rewrite /operation_forgery_witness_invariant; smt().
  qed.
end section DirectOperationBridgeCharacterization.

section DirectOperationBridgePrimitiveEquality.
  declare module A <: ADAPTIVE_ORIGIN_UNAUTHORIZED_ADVERSARY.
  declare module S <: SIGNATURE_SCHEME.
  declare module H <: NODE_HASH.

  module BR = OriginOperationDirectBridgeGame(A, S, H).
  module EUF =
    PG.MultiUserEUFCMAGame(BSignOriginOperationDirect(A, H), S).

  (* Erasing the ghost observations leaves exactly the named primitive game:
     identical oracle initialization, reduction call, final logs, optional
     candidate check, and success predicate. *)
  lemma origin_direct_bridge_win_exactly_eufcma
      &m (initial : protocol_state) :
    Pr[
      BR.main(initial) @ &m : res.`odobr_win
    ] =
    Pr[
      EUF.main(initial) @ &m : res
    ].
  proof.
    byequiv
      (_ : ={initial_state, glob A, glob S, glob H} ==>
           res{1}.`odobr_win = res{2}) => //.
    proc.
    inline *.
    sim.
  qed.
end section DirectOperationBridgePrimitiveEquality.

section DirectOperationPartitionLink.
  declare module A <: ADAPTIVE_ORIGIN_UNAUTHORIZED_ADVERSARY.
  declare module S <: SIGNATURE_SCHEME.
  declare module H <: NODE_HASH.

  module GP = UnauthorizedOriginPartitionGame(A, S, H).
  module BR = OriginOperationDirectBridgeGame(A, S, H).
  module EUF =
    PG.MultiUserEUFCMAGame(BSignOriginOperationDirect(A, H), S).

  (* The partition game and bridge run the same origin-aware environment.  The
     bridge only reads the final primitive logs and returns ghost fields after
     the adaptive attack. *)
  lemma origin_partition_bad_operation_exactly_direct_bridge_bad
      &m (initial : protocol_state) :
    Pr[
      GP.main(initial) @ &m : res.`opr_bad_operation
    ] =
    Pr[
      BR.main(initial) @ &m : res.`odobr_bad
    ].
  proof.
    byequiv
      (_ : ={initial_state, glob A, glob S, glob H} ==>
           res{1}.`opr_bad_operation = res{2}.`odobr_bad) => //.
    proc.
    inline *.
    sim.
  qed.

  lemma origin_direct_bridge_bad_probability_equals_win
      &m (initial : protocol_state) :
    Pr[
      BR.main(initial) @ &m : res.`odobr_bad
    ] =
    Pr[
      BR.main(initial) @ &m : res.`odobr_win
    ].
  proof.
    have hbad_not_win :
      Pr[
        BR.main(initial) @ &m :
          res.`odobr_bad /\ ! res.`odobr_win
      ] = 0%r.
    + byphoare
        (_ : initial_state = initial ==>
          ! (res.`odobr_bad /\ ! res.`odobr_win)) => //=.
      conseq (origin_direct_bridge_characterization initial) => /#.

    have hwin_not_bad :
      Pr[
        BR.main(initial) @ &m :
          res.`odobr_win /\ ! res.`odobr_bad
      ] = 0%r.
    + byphoare
        (_ : initial_state = initial ==>
          ! (res.`odobr_win /\ ! res.`odobr_bad)) => //=.
      conseq (origin_direct_bridge_characterization initial) => /#.

    have hbad_le :
      Pr[BR.main(initial) @ &m : res.`odobr_bad] <=
      Pr[BR.main(initial) @ &m : res.`odobr_win] +
      Pr[
        BR.main(initial) @ &m :
          res.`odobr_bad /\ ! res.`odobr_win
      ].
    + have hsub :
        Pr[BR.main(initial) @ &m : res.`odobr_bad] <=
        Pr[
          BR.main(initial) @ &m :
            res.`odobr_win \/
            (res.`odobr_bad /\ ! res.`odobr_win)
        ].
      + rewrite Pr [mu_sub]=> /#.
      have hunion :
        Pr[
          BR.main(initial) @ &m :
            res.`odobr_win \/
            (res.`odobr_bad /\ ! res.`odobr_win)
        ] <=
        Pr[BR.main(initial) @ &m : res.`odobr_win] +
        Pr[
          BR.main(initial) @ &m :
            res.`odobr_bad /\ ! res.`odobr_win
        ].
      + rewrite Pr [mu_or].
        smt(ge0_mu).
      smt().

    have hwin_le :
      Pr[BR.main(initial) @ &m : res.`odobr_win] <=
      Pr[BR.main(initial) @ &m : res.`odobr_bad] +
      Pr[
        BR.main(initial) @ &m :
          res.`odobr_win /\ ! res.`odobr_bad
      ].
    + have hsub :
        Pr[BR.main(initial) @ &m : res.`odobr_win] <=
        Pr[
          BR.main(initial) @ &m :
            res.`odobr_bad \/
            (res.`odobr_win /\ ! res.`odobr_bad)
        ].
      + rewrite Pr [mu_sub]=> /#.
      have hunion :
        Pr[
          BR.main(initial) @ &m :
            res.`odobr_bad \/
            (res.`odobr_win /\ ! res.`odobr_bad)
        ] <=
        Pr[BR.main(initial) @ &m : res.`odobr_bad] +
        Pr[
          BR.main(initial) @ &m :
            res.`odobr_win /\ ! res.`odobr_bad
        ].
      + rewrite Pr [mu_or].
        smt(ge0_mu).
      smt().

    smt().
  qed.

  (* This is the first non-decorative A2 theorem over the exact A0 partition
     event: its left side is the real game's bad-operation field, and its right
     side is the concrete named multi-user EUF-CMA game. *)
  lemma origin_partition_bad_operation_exactly_multi_user_eufcma
      &m (initial : protocol_state) :
    Pr[
      GP.main(initial) @ &m : res.`opr_bad_operation
    ] =
    Pr[
      EUF.main(initial) @ &m : res
    ].
  proof.
    rewrite
      (origin_partition_bad_operation_exactly_direct_bridge_bad &m initial)
      (origin_direct_bridge_bad_probability_equals_win &m initial).
    exact (origin_direct_bridge_win_exactly_eufcma &m initial).
  qed.
end section DirectOperationPartitionLink.
