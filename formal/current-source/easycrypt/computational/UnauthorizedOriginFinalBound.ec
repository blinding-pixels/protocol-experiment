require import AllCore List FSet.
require import ProtocolTypes ProtocolPrimitives UnauthorizedOriginGame UnauthorizedOriginPartition.
require import UnauthorizedSignatureReduction OriginOperationDirectInvariant.
require import OriginOperationDirectReduction OriginFactVerificationEvidence OriginFactSelection OriginFactBadStep OriginFactWitnessGame OriginFactReductionWitness.
require import OriginHashHop.

import PG.

(* Probability composition for the exact origin-aware A0 experiment.  The
   partition invariant, A5-zero invariant, and union bounds are all proved over
   one execution of [UnauthorizedOriginPartitionGame]. *)
section OriginFinalProbabilityBound.
  declare module A <: ADAPTIVE_ORIGIN_UNAUTHORIZED_ADVERSARY.
  declare module S <: ProtocolPrimitives.SIGNATURE_SCHEME.
  declare module H <: ProtocolPrimitives.NODE_HASH.

  module GF = UnauthorizedOriginPartitionGame(A, S, H).
  module GH = UnauthorizedOriginA1HashEvidence(A, S, H).
  module EUFOP =
    PG.MultiUserEUFCMAGame(BSignOriginOperationDirect(A, H), S).
  module EUFFACT =
    PG.MultiUserEUFCMAGame(BSignOriginFactWitness(A, H), S).
  module COLL = PG.NodeCollisionGame(BHashOrigin(A, S), H).

  lemma origin_real_probability_le_signature_bad_sum
      &m (initial : protocol_state) :
    Pr[GF.main(initial) @ &m : res.`opr_real] <=
      Pr[GF.main(initial) @ &m : res.`opr_bad_operation] +
      Pr[GF.main(initial) @ &m : res.`opr_bad_fact].
  proof.
    have hpartition :
      Pr[
        GF.main(initial) @ &m :
          ! origin_partition_holds
              res.`opr_real
              res.`opr_bad_operation
              res.`opr_bad_fact
              res.`opr_ideal
      ] = 0%r.
    + byphoare
        (_ : initial_state = initial ==>
          origin_partition_holds
            res.`opr_real
            res.`opr_bad_operation
            res.`opr_bad_fact
            res.`opr_ideal) => //=.
      proc.
      call (_ :
        origin_partition_holds
          GF.O.unauthorized_accepted
          GF.O.bad_operation_signature
          GF.O.bad_fact_signature
          GF.O.ideal_unauthorized).
      * exact UnauthorizedOriginPartition.origin_sign_operation_preserves_partition.
      * exact UnauthorizedOriginPartition.origin_sign_fact_preserves_partition.
      * exact UnauthorizedOriginPartition.origin_submit_preserves_partition.
      auto; rewrite /origin_partition_holds.

    have hideal :
      Pr[GF.main(initial) @ &m : res.`opr_ideal] = 0%r.
    + byphoare (_ : initial_state = initial ==> ! res.`opr_ideal) => //=.
      proc.
      call (_ : ! GF.O.ideal_unauthorized).
      * exact UnauthorizedOriginPartition.origin_sign_operation_preserves_no_ideal.
      * exact UnauthorizedOriginPartition.origin_sign_fact_preserves_no_ideal.
      * exact UnauthorizedOriginPartition.origin_submit_preserves_no_ideal.
      auto.

    have hsub :
      Pr[GF.main(initial) @ &m : res.`opr_real] <=
      Pr[
        GF.main(initial) @ &m :
          (res.`opr_bad_operation \/ res.`opr_bad_fact \/ res.`opr_ideal) \/
          ! origin_partition_holds
              res.`opr_real
              res.`opr_bad_operation
              res.`opr_bad_fact
              res.`opr_ideal
      ].
    + rewrite Pr [mu_sub]=> /#.

    have hunion :
      Pr[
        GF.main(initial) @ &m :
          (res.`opr_bad_operation \/ res.`opr_bad_fact \/ res.`opr_ideal) \/
          ! origin_partition_holds
              res.`opr_real
              res.`opr_bad_operation
              res.`opr_bad_fact
              res.`opr_ideal
      ] <=
        Pr[
          GF.main(initial) @ &m :
            res.`opr_bad_operation \/ res.`opr_bad_fact \/ res.`opr_ideal
        ] +
        Pr[
          GF.main(initial) @ &m :
            ! origin_partition_holds
                res.`opr_real
                res.`opr_bad_operation
                res.`opr_bad_fact
                res.`opr_ideal
        ].
    + rewrite Pr [mu_or].
      smt(ge0_mu).

    have hbad :
      Pr[
        GF.main(initial) @ &m :
          res.`opr_bad_operation \/ res.`opr_bad_fact \/ res.`opr_ideal
      ] <=
        Pr[GF.main(initial) @ &m : res.`opr_bad_operation] +
        Pr[GF.main(initial) @ &m : res.`opr_bad_fact] +
        Pr[GF.main(initial) @ &m : res.`opr_ideal].
    + rewrite !mu_or.
      smt(ge0_mu).

    smt().
  qed.

  lemma origin_real_probability_le_operation_eufcma_plus_fact_bad
      &m (initial : protocol_state) :
    Pr[GF.main(initial) @ &m : res.`opr_real] <=
      Pr[EUFOP.main(initial) @ &m : res] +
      Pr[GF.main(initial) @ &m : res.`opr_bad_fact].
  proof.
    have hreal := origin_real_probability_le_signature_bad_sum &m initial.
    have hop :=
      origin_partition_bad_operation_exactly_multi_user_eufcma &m initial.
    smt().
  qed.

  (* Both signature-origin branches are concrete primitive experiments.  The
     ideal branch is probability zero by the same A0 execution invariant. *)
  lemma origin_real_probability_le_operation_and_fact_eufcma
      &m (initial : protocol_state) :
    Pr[GF.main(initial) @ &m : res.`opr_real] <=
      Pr[EUFOP.main(initial) @ &m : res] +
      Pr[EUFFACT.main(initial) @ &m : res].
  proof.
    have hreal :=
      origin_real_probability_le_operation_eufcma_plus_fact_bad &m initial.
    have hfact :=
      origin_partition_bad_fact_exactly_multi_user_eufcma &m initial.
    smt().
  qed.

  (* Full A0--A5 computational bound.  A0 is split from A1 on the concrete
     collision event in the exact production hash transcript; A2 and A3 are
     the two exact multi-user EUF-CMA reductions; A5 contributes zero. *)
  lemma origin_unauthorized_probability_bound
      &m (initial : protocol_state) :
    Pr[GF.main(initial) @ &m : res.`opr_real] <=
        Pr[EUFOP.main(initial) @ &m : res]
      + Pr[EUFFACT.main(initial) @ &m : res]
      + Pr[COLL.main(initial) @ &m : res].
  proof.
    have hreal_hash :=
      origin_partition_real_exactly_hash_evidence_real
        (A := A) (S := S) (H := H) &m initial.
    have hsplit :=
      origin_hash_evidence_real_le_safe_plus_bad
        (A := A) (S := S) (H := H) &m initial.
    have hsafe :=
      origin_hash_safe_real_le_partition_real
        (A := A) (S := S) (H := H) &m initial.
    have hsignatures :=
      origin_real_probability_le_operation_and_fact_eufcma &m initial.
    have hcollision :=
      origin_hash_bad_probability_exactly_collision
        (A := A) (S := S) (H := H) &m initial.
    smt().
  qed.
end section OriginFinalProbabilityBound.
