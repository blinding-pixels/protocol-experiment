require import AllCore List FSet.
require import ProtocolTypes CanonicalEncoding ProtocolPrimitives UnauthorizedOriginGame UnauthorizedOriginPartition.
require import UnauthorizedSignatureReduction OriginOperationDirectInvariant.
require import OriginOperationDirectReduction OriginFactReductionWitness.
require import UnauthorizedOriginHashReduction.

import PG.

(* Deliverable A uses native multi-user primitive games: every verification key
   and every accepted fact is forwarded to one logged primitive experiment.
   No key/user guessing is performed by either reduction, so both multiplicative
   factors are exactly one. *)
op q_operation_signature_factor : real = 1%r.
op q_fact_signature_factor : real = 1%r.

(* Canonical operation encoding is an injective datatype constructor in this
   EasyCrypt abstraction.  Rust byte-level correspondence remains a separate
   implementation obligation, but the model-level encoding-failure term is
   exactly zero. *)
op encoding_failure_probability : real = 0%r.

lemma encoding_failure_probability_zero :
  encoding_failure_probability = 0%r.
proof. by rewrite /encoding_failure_probability. qed.

lemma distinct_envelopes_have_distinct_canonical_encodings
    (left right : operation_envelope) :
  left <> right => encode_operation left <> encode_operation right.
proof.
  move=> different equal_encoding.
  have same := encode_operation_injective left right equal_encoding.
  by smt().
qed.

(* One instrumented execution contains A0's exact real bit, A1's concrete
   collision event, A2/A3's exact origin events, and the A5 event.  Hash logging
   is private ghost state and does not alter any adversary-facing oracle
   response.  The ideal component is intentionally the collision-free A5
   branch: once a collision occurs, the execution is charged to A1 rather than
   silently reusing an ambiguous node identifier in the ideal semantics. *)
type origin_deliverable_a_result = {
  odar_real : bool;
  odar_bad_hash : bool;
  odar_bad_operation : bool;
  odar_bad_fact : bool;
  odar_ideal : bool
}.

pred origin_deliverable_a_partition_holds
    (real bad_hash bad_operation bad_fact ideal : bool) =
  real => bad_hash \/ bad_operation \/ bad_fact \/ ideal.

module UnauthorizedOriginDeliverableAGame(
  A : ADAPTIVE_ORIGIN_UNAUTHORIZED_ADVERSARY,
  S : SIGNATURE_SCHEME,
  H : NODE_HASH
) = {
  module SO = PG.LoggedSignatureOracle(S)
  module HLog = PG.LoggedNodeHash(H)
  module O = OriginTrackedCandidateEnvironment(SO, HLog)
  module A = A(O)

  proc main(initial_state : protocol_state) : origin_deliverable_a_result = {
    var hash_queries : PG.node_hash_query list;
    var collision : PG.node_collision option;

    SO.init();
    HLog.init();
    O.init(initial_state);
    A.attack();
    hash_queries <@ HLog.get_queries();
    collision <- PG.find_node_collision_pair hash_queries;

    return
      {| odar_real = O.unauthorized_accepted;
         odar_bad_hash = collision <> None;
         odar_bad_operation = O.bad_operation_signature;
         odar_bad_fact = O.bad_fact_signature;
         odar_ideal = O.ideal_unauthorized /\ collision = None |};
  }
}.

section DeliverableAPartition.
  declare module A <: ADAPTIVE_ORIGIN_UNAUTHORIZED_ADVERSARY.
  declare module S <: SIGNATURE_SCHEME.
  declare module H <: NODE_HASH.

  module G = UnauthorizedOriginDeliverableAGame(A, S, H).

  lemma origin_deliverable_a_main_partition
      (initial : protocol_state) :
    hoare [G.main :
      initial_state = initial ==>
      origin_deliverable_a_partition_holds
        res.`odar_real
        res.`odar_bad_hash
        res.`odar_bad_operation
        res.`odar_bad_fact
        res.`odar_ideal].
  proof.
    proc.
    inline G.HLog.get_queries.
    call (_ :
      origin_partition_holds
        G.O.unauthorized_accepted
        G.O.bad_operation_signature
        G.O.bad_fact_signature
        G.O.ideal_unauthorized).
    + exact origin_sign_operation_preserves_partition.
    + exact origin_sign_fact_preserves_partition.
    + exact origin_submit_preserves_partition.
    auto=> />.
    rewrite /origin_deliverable_a_partition_holds /origin_partition_holds.
    smt().
  qed.

  lemma origin_deliverable_a_ideal_probability_zero
      &m (initial : protocol_state) :
    Pr[G.main(initial) @ &m : res.`odar_ideal] = 0%r.
  proof.
    byphoare
      (_ : initial_state = initial ==> ! res.`odar_ideal) => //=.
    proc.
    inline G.HLog.get_queries.
    call (_ : ! G.O.ideal_unauthorized).
    + exact origin_sign_operation_preserves_no_ideal.
    + exact origin_sign_fact_preserves_no_ideal.
    + exact origin_submit_preserves_no_ideal.
    auto.
  qed.

  lemma origin_deliverable_a_real_probability_le_bad_sum
      &m (initial : protocol_state) :
    Pr[G.main(initial) @ &m : res.`odar_real] <=
        Pr[G.main(initial) @ &m : res.`odar_bad_hash]
      + Pr[G.main(initial) @ &m : res.`odar_bad_operation]
      + Pr[G.main(initial) @ &m : res.`odar_bad_fact]
      + Pr[G.main(initial) @ &m : res.`odar_ideal].
  proof.
    have hpartition :
      Pr[
        G.main(initial) @ &m :
          ! origin_deliverable_a_partition_holds
              res.`odar_real
              res.`odar_bad_hash
              res.`odar_bad_operation
              res.`odar_bad_fact
              res.`odar_ideal
      ] = 0%r.
    + byphoare
        (_ : initial_state = initial ==>
          origin_deliverable_a_partition_holds
            res.`odar_real
            res.`odar_bad_hash
            res.`odar_bad_operation
            res.`odar_bad_fact
            res.`odar_ideal) => //=.
      exact (origin_deliverable_a_main_partition initial).

    have hsub :
      Pr[G.main(initial) @ &m : res.`odar_real] <=
      Pr[
        G.main(initial) @ &m :
          (res.`odar_bad_hash \/
           res.`odar_bad_operation \/
           res.`odar_bad_fact \/
           res.`odar_ideal) \/
          ! origin_deliverable_a_partition_holds
              res.`odar_real
              res.`odar_bad_hash
              res.`odar_bad_operation
              res.`odar_bad_fact
              res.`odar_ideal
      ].
    + rewrite Pr [mu_sub]=> /#.

    have hunion :
      Pr[
        G.main(initial) @ &m :
          (res.`odar_bad_hash \/
           res.`odar_bad_operation \/
           res.`odar_bad_fact \/
           res.`odar_ideal) \/
          ! origin_deliverable_a_partition_holds
              res.`odar_real
              res.`odar_bad_hash
              res.`odar_bad_operation
              res.`odar_bad_fact
              res.`odar_ideal
      ] <=
        Pr[
          G.main(initial) @ &m :
            res.`odar_bad_hash \/
            res.`odar_bad_operation \/
            res.`odar_bad_fact \/
            res.`odar_ideal
        ] +
        Pr[
          G.main(initial) @ &m :
            ! origin_deliverable_a_partition_holds
                res.`odar_real
                res.`odar_bad_hash
                res.`odar_bad_operation
                res.`odar_bad_fact
                res.`odar_ideal
        ].
    + rewrite Pr [mu_or].
      smt(ge0_mu).

    have hbad :
      Pr[
        G.main(initial) @ &m :
          res.`odar_bad_hash \/
          res.`odar_bad_operation \/
          res.`odar_bad_fact \/
          res.`odar_ideal
      ] <=
          Pr[G.main(initial) @ &m : res.`odar_bad_hash]
        + Pr[G.main(initial) @ &m : res.`odar_bad_operation]
        + Pr[G.main(initial) @ &m : res.`odar_bad_fact]
        + Pr[G.main(initial) @ &m : res.`odar_ideal].
    + rewrite !mu_or.
      smt(ge0_mu).

    smt().
  qed.
end section DeliverableAPartition.

section DeliverableADistributionLinks.
  declare module A <: ADAPTIVE_ORIGIN_UNAUTHORIZED_ADVERSARY.
  declare module S <: SIGNATURE_SCHEME.
  declare module H <: NODE_HASH.

  module G = UnauthorizedOriginDeliverableAGame(A, S, H).
  module GP = UnauthorizedOriginPartitionGame(A, S, H).
  module GH = UnauthorizedOriginA1HashEvidence(A, S, H).
  module EUFOP =
    PG.MultiUserEUFCMAGame(BSignOriginOperationDirect(A, H), S).
  module EUFFACT =
    PG.MultiUserEUFCMAGame(BSignOriginFactWitness(A, H), S).
  module COLL = PG.NodeCollisionGame(BHashOrigin(A, S), H).

  lemma origin_deliverable_a_real_exactly_a0
      &m (initial : protocol_state) :
    Pr[G.main(initial) @ &m : res.`odar_real] =
    Pr[GP.main(initial) @ &m : res.`opr_real].
  proof.
    byequiv
      (_ : ={initial_state, glob A, glob S, glob H} ==>
           res{1}.`odar_real = res{2}.`opr_real) => //.
    proc.
    inline *.
    sim.
  qed.

  lemma origin_deliverable_a_bad_operation_exactly_a2
      &m (initial : protocol_state) :
    Pr[G.main(initial) @ &m : res.`odar_bad_operation] =
    Pr[EUFOP.main(initial) @ &m : res].
  proof.
    have hgame :
      Pr[G.main(initial) @ &m : res.`odar_bad_operation] =
      Pr[GP.main(initial) @ &m : res.`opr_bad_operation].
    + byequiv
        (_ : ={initial_state, glob A, glob S, glob H} ==>
             res{1}.`odar_bad_operation = res{2}.`opr_bad_operation) => //.
      proc.
      inline *.
      sim.
    rewrite hgame.
    exact (origin_partition_bad_operation_exactly_multi_user_eufcma
      &m initial).
  qed.

  lemma origin_deliverable_a_bad_fact_exactly_a3
      &m (initial : protocol_state) :
    Pr[G.main(initial) @ &m : res.`odar_bad_fact] =
    Pr[EUFFACT.main(initial) @ &m : res].
  proof.
    have hgame :
      Pr[G.main(initial) @ &m : res.`odar_bad_fact] =
      Pr[GP.main(initial) @ &m : res.`opr_bad_fact].
    + byequiv
        (_ : ={initial_state, glob A, glob S, glob H} ==>
             res{1}.`odar_bad_fact = res{2}.`opr_bad_fact) => //.
      proc.
      inline *.
      sim.
    rewrite hgame.
    exact (origin_partition_bad_fact_exactly_multi_user_eufcma
      &m initial).
  qed.

  lemma origin_deliverable_a_bad_hash_exactly_a1
      &m (initial : protocol_state) :
    Pr[G.main(initial) @ &m : res.`odar_bad_hash] =
    Pr[COLL.main(initial) @ &m : res].
  proof.
    have hgame :
      Pr[G.main(initial) @ &m : res.`odar_bad_hash] =
      Pr[GH.main(initial) @ &m : res.`2].
    + byequiv
        (_ : ={initial_state, glob A, glob S, glob H} ==>
             res{1}.`odar_bad_hash = res{2}.`2) => //.
      proc.
      inline *.
      sim.
    rewrite hgame.
    exact (origin_bad_hash_exactly_reduces_to_node_collision &m initial).
  qed.

  (* Public Deliverable A theorem.  The left side is the exact A0
     unauthorized-acceptance probability.  Every nonzero RHS term is the
     probability of a concrete named primitive game run with a concrete
     reduction adversary.  The two native multi-user reductions incur factor
     one, and deterministic canonical encoding contributes exactly zero. *)
  lemma adv_unauthorized_origin_bound
      &m (initial : protocol_state) :
    Pr[GP.main(initial) @ &m : res.`opr_real] <=
        q_operation_signature_factor *
          Pr[EUFOP.main(initial) @ &m : res]
      + q_fact_signature_factor *
          Pr[EUFFACT.main(initial) @ &m : res]
      + Pr[COLL.main(initial) @ &m : res]
      + encoding_failure_probability.
  proof.
    have hreal :=
      origin_deliverable_a_real_probability_le_bad_sum &m initial.
    have hreal_eq := origin_deliverable_a_real_exactly_a0 &m initial.
    have hop := origin_deliverable_a_bad_operation_exactly_a2 &m initial.
    have hfact := origin_deliverable_a_bad_fact_exactly_a3 &m initial.
    have hhash := origin_deliverable_a_bad_hash_exactly_a1 &m initial.
    have hideal := origin_deliverable_a_ideal_probability_zero &m initial.
    rewrite /q_operation_signature_factor /q_fact_signature_factor
      /encoding_failure_probability.
    smt().
  qed.
end section DeliverableADistributionLinks.
