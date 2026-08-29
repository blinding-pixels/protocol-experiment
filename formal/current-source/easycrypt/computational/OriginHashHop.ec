require import AllCore List FSet.
require import ProtocolTypes ProtocolPrimitives UnauthorizedSignatureReduction.
require import UnauthorizedOriginPartition UnauthorizedOriginHashReduction.

import PG.

section OriginHashHop.
  declare module A <: ADAPTIVE_ORIGIN_UNAUTHORIZED_ADVERSARY.
  declare module S <: SIGNATURE_SCHEME.
  declare module H <: NODE_HASH.

  module GP = UnauthorizedOriginPartitionGame(A, S, H).
  module GH = UnauthorizedOriginA1HashEvidence(A, S, H).
  module COLL = PG.NodeCollisionGame(BHashOrigin(A, S), H).

  (* Wrapping the production node hash with its exact query logger does not
     change the A0 execution or real win bit.  The extra state is private and
     records precisely the hashes already requested by accepted operations. *)
  lemma origin_partition_real_exactly_hash_evidence_real
      &m (initial : protocol_state) :
    Pr[
      GP.main(initial) @ &m : res.`opr_real
    ] =
    Pr[
      GH.main(initial) @ &m : res.`1
    ].
  proof.
    byequiv
      (_ : ={initial_state, glob A, glob S, glob H} ==>
           res{1}.`opr_real = res{2}.`1) => //.
    proc.
    inline *.
    sim.
  qed.

  (* A1 is A0 with an abort on the concrete collision event extracted from the
     exact production hash transcript.  This is a genuine fundamental-lemma
     split, not an unrelated nonnegative term appended to the final bound. *)
  lemma origin_hash_evidence_real_le_safe_plus_bad
      &m (initial : protocol_state) :
    Pr[
      GH.main(initial) @ &m : res.`1
    ] <=
      Pr[
        GH.main(initial) @ &m : res.`1 /\ ! res.`2
      ] +
      Pr[
        GH.main(initial) @ &m : res.`2
      ].
  proof.
    have hsub :
      Pr[GH.main(initial) @ &m : res.`1] <=
      Pr[
        GH.main(initial) @ &m :
          (res.`1 /\ ! res.`2) \/ res.`2
      ].
    + rewrite Pr [mu_sub]=> /#.
    have hunion :
      Pr[
        GH.main(initial) @ &m :
          (res.`1 /\ ! res.`2) \/ res.`2
      ] <=
      Pr[GH.main(initial) @ &m : res.`1 /\ ! res.`2] +
      Pr[GH.main(initial) @ &m : res.`2].
    + rewrite Pr [mu_or].
      smt(ge0_mu).
    smt().
  qed.

  lemma origin_hash_safe_real_le_partition_real
      &m (initial : protocol_state) :
    Pr[
      GH.main(initial) @ &m : res.`1 /\ ! res.`2
    ] <=
    Pr[
      GP.main(initial) @ &m : res.`opr_real
    ].
  proof.
    have hsafe :
      Pr[GH.main(initial) @ &m : res.`1 /\ ! res.`2] <=
      Pr[GH.main(initial) @ &m : res.`1].
    + rewrite Pr [mu_sub]=> /#.
    have hreal :=
      origin_partition_real_exactly_hash_evidence_real &m initial.
    smt().
  qed.

  lemma origin_hash_bad_probability_exactly_collision
      &m (initial : protocol_state) :
    Pr[
      GH.main(initial) @ &m : res.`2
    ] =
    Pr[
      COLL.main(initial) @ &m : res
    ].
  proof.
    exact (origin_bad_hash_exactly_reduces_to_node_collision
      (A := A) (S := S) (H := H) &m initial).
  qed.
end section OriginHashHop.
