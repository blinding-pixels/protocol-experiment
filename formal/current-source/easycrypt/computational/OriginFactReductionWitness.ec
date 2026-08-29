require import AllCore List FSet.
require import ProtocolTypes CanonicalEncoding ProtocolPrimitives AuthorizationState.
require import UnauthorizedSignatureReduction UnauthorizedOriginGame UnauthorizedOriginPartition.
require import OriginFactWitnessGame.

import PG.

section FactWitnessReductionAdversary.
  declare module A <: ADAPTIVE_ORIGIN_UNAUTHORIZED_ADVERSARY.
  declare module S <: SIGNATURE_SCHEME.
  declare module H <: NODE_HASH.

  module SOR = PG.LoggedSignatureOracle(S).
  module B = BSignOriginFactWitness(A, H, SOR).

  lemma fact_witness_reduction_forge_characterization
      (initial : protocol_state) :
    hoare [B.forge :
      initial_state = initial ==>
      fact_forgery_witness_invariant
        B.O.Base.unauthorized_accepted
        B.O.Base.bad_fact_signature
        res
        SOR.sign_queries SOR.verify_queries].
  proof.
    proc.
    call (_ :
      fact_forgery_witness_invariant
        B.O.Base.unauthorized_accepted
        B.O.Base.bad_fact_signature
        B.O.fact_forgery
        SOR.sign_queries SOR.verify_queries).
    + exact fact_witness_sign_operation_preserves_invariant.
    + exact fact_witness_sign_fact_preserves_invariant.
    + move=> input_operation input_view.
      exact (fact_witness_submit_preserves_invariant
        input_operation input_view).
    inline B.O.init B.O.Base.init B.O.Base.Base.init.
    auto; rewrite /fact_forgery_witness_invariant.
  qed.
end section FactWitnessReductionAdversary.

type fact_witness_bridge_result = {
  fwbr_bad : bool;
  fwbr_real : bool;
  fwbr_win : bool
}.

module OriginFactWitnessBridgeGame(
  A : ADAPTIVE_ORIGIN_UNAUTHORIZED_ADVERSARY,
  S : SIGNATURE_SCHEME,
  H : NODE_HASH
) = {
  module SO = PG.LoggedSignatureOracle(S)
  module B = BSignOriginFactWitness(A, H, SO)

  proc main(
    initial_state : protocol_state
  ) : fact_witness_bridge_result = {
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
      {| fwbr_bad = B.O.Base.bad_fact_signature;
         fwbr_real = B.O.Base.unauthorized_accepted;
         fwbr_win = win |};
  }
}.

section FactWitnessBridgeCharacterization.
  declare module A <: ADAPTIVE_ORIGIN_UNAUTHORIZED_ADVERSARY.
  declare module S <: SIGNATURE_SCHEME.
  declare module H <: NODE_HASH.

  module R = OriginFactWitnessBridgeGame(A, S, H).

  lemma fact_witness_bridge_characterization
      (initial : protocol_state) :
    hoare [R.main :
      initial_state = initial ==>
         res.`fwbr_bad = res.`fwbr_win
      /\ (res.`fwbr_bad => res.`fwbr_real)].
  proof.
    proc.
    inline R.SO.init.
    call (fact_witness_reduction_forge_characterization initial).
    inline R.SO.get_sign_queries R.SO.get_verify_queries.
    auto; rewrite /fact_forgery_witness_invariant; smt().
  qed.
end section FactWitnessBridgeCharacterization.

section FactWitnessPrimitiveEquality.
  declare module A <: ADAPTIVE_ORIGIN_UNAUTHORIZED_ADVERSARY.
  declare module S <: SIGNATURE_SCHEME.
  declare module H <: NODE_HASH.

  module BR = OriginFactWitnessBridgeGame(A, S, H).
  module EUF =
    PG.MultiUserEUFCMAGame(BSignOriginFactWitness(A, H), S).

  lemma fact_witness_bridge_win_exactly_eufcma
      &m (initial : protocol_state) :
    Pr[
      BR.main(initial) @ &m : res.`fwbr_win
    ] =
    Pr[
      EUF.main(initial) @ &m : res
    ].
  proof.
    byequiv
      (_ : ={initial_state, glob A, glob S, glob H} ==>
           res{1}.`fwbr_win = res{2}) => //.
    proc.
    inline *.
    sim.
  qed.
end section FactWitnessPrimitiveEquality.

section FactWitnessPartitionLink.
  declare module A <: ADAPTIVE_ORIGIN_UNAUTHORIZED_ADVERSARY.
  declare module S <: SIGNATURE_SCHEME.
  declare module H <: NODE_HASH.

  module GP = UnauthorizedOriginPartitionGame(A, S, H).
  module BR = OriginFactWitnessBridgeGame(A, S, H).
  module EUF =
    PG.MultiUserEUFCMAGame(BSignOriginFactWitness(A, H), S).

  (* The wrapper adds only a private retained witness.  Its public procedures
     delegate to the same origin-aware production environment and therefore
     preserve the exact A0 fact-bad distribution. *)
  lemma origin_partition_bad_fact_exactly_witness_bridge_bad
      &m (initial : protocol_state) :
    Pr[
      GP.main(initial) @ &m : res.`opr_bad_fact
    ] =
    Pr[
      BR.main(initial) @ &m : res.`fwbr_bad
    ].
  proof.
    byequiv
      (_ : ={initial_state, glob A, glob S, glob H} ==>
           res{1}.`opr_bad_fact = res{2}.`fwbr_bad) => //.
    proc.
    inline *.
    sim.
  qed.

  lemma origin_witness_bridge_bad_probability_equals_win
      &m (initial : protocol_state) :
    Pr[
      BR.main(initial) @ &m : res.`fwbr_bad
    ] =
    Pr[
      BR.main(initial) @ &m : res.`fwbr_win
    ].
  proof.
    have hbad_not_win :
      Pr[
        BR.main(initial) @ &m :
          res.`fwbr_bad /\ ! res.`fwbr_win
      ] = 0%r.
    + byphoare
        (_ : initial_state = initial ==>
          ! (res.`fwbr_bad /\ ! res.`fwbr_win)) => //=.
      conseq (fact_witness_bridge_characterization initial) => /#.

    have hwin_not_bad :
      Pr[
        BR.main(initial) @ &m :
          res.`fwbr_win /\ ! res.`fwbr_bad
      ] = 0%r.
    + byphoare
        (_ : initial_state = initial ==>
          ! (res.`fwbr_win /\ ! res.`fwbr_bad)) => //=.
      conseq (fact_witness_bridge_characterization initial) => /#.

    have hbad_le :
      Pr[BR.main(initial) @ &m : res.`fwbr_bad] <=
      Pr[BR.main(initial) @ &m : res.`fwbr_win] +
      Pr[
        BR.main(initial) @ &m :
          res.`fwbr_bad /\ ! res.`fwbr_win
      ].
    + have hsub :
        Pr[BR.main(initial) @ &m : res.`fwbr_bad] <=
        Pr[
          BR.main(initial) @ &m :
            res.`fwbr_win \/
            (res.`fwbr_bad /\ ! res.`fwbr_win)
        ].
      + rewrite Pr [mu_sub]=> /#.
      have hunion :
        Pr[
          BR.main(initial) @ &m :
            res.`fwbr_win \/
            (res.`fwbr_bad /\ ! res.`fwbr_win)
        ] <=
        Pr[BR.main(initial) @ &m : res.`fwbr_win] +
        Pr[
          BR.main(initial) @ &m :
            res.`fwbr_bad /\ ! res.`fwbr_win
        ].
      + rewrite Pr [mu_or].
        smt(ge0_mu).
      smt().

    have hwin_le :
      Pr[BR.main(initial) @ &m : res.`fwbr_win] <=
      Pr[BR.main(initial) @ &m : res.`fwbr_bad] +
      Pr[
        BR.main(initial) @ &m :
          res.`fwbr_win /\ ! res.`fwbr_bad
      ].
    + have hsub :
        Pr[BR.main(initial) @ &m : res.`fwbr_win] <=
        Pr[
          BR.main(initial) @ &m :
            res.`fwbr_bad \/
            (res.`fwbr_win /\ ! res.`fwbr_bad)
        ].
      + rewrite Pr [mu_sub]=> /#.
      have hunion :
        Pr[
          BR.main(initial) @ &m :
            res.`fwbr_bad \/
            (res.`fwbr_win /\ ! res.`fwbr_bad)
        ] <=
        Pr[BR.main(initial) @ &m : res.`fwbr_bad] +
        Pr[
          BR.main(initial) @ &m :
            res.`fwbr_win /\ ! res.`fwbr_bad
        ].
      + rewrite Pr [mu_or].
        smt(ge0_mu).
      smt().

    smt().
  qed.

  lemma origin_partition_bad_fact_exactly_multi_user_eufcma
      &m (initial : protocol_state) :
    Pr[
      GP.main(initial) @ &m : res.`opr_bad_fact
    ] =
    Pr[
      EUF.main(initial) @ &m : res
    ].
  proof.
    rewrite
      (origin_partition_bad_fact_exactly_witness_bridge_bad &m initial)
      (origin_witness_bridge_bad_probability_equals_win &m initial).
    exact (fact_witness_bridge_win_exactly_eufcma &m initial).
  qed.
end section FactWitnessPartitionLink.
