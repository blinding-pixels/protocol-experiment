require import AllCore List FSet.
require import ProtocolTypes CanonicalEncoding ProtocolPrimitives AuthorizationState.
require import UnauthorizedSignatureReduction UnauthorizedOriginGame.

import PG.

pred origin_partition_holds
    (real bad_operation bad_fact ideal : bool) =
  real => bad_operation \/ bad_fact \/ ideal.

lemma origin_partition_update
    (real bad_operation bad_fact ideal : bool)
    (semantic operation_originated facts_originated ideal_authorized : bool) :
  origin_partition_holds real bad_operation bad_fact ideal =>
  (semantic =>
     ! operation_originated \/ ! facts_originated \/ ! ideal_authorized) =>
  origin_partition_holds
    (real \/ semantic)
    (bad_operation \/ (semantic /\ ! operation_originated))
    (bad_fact \/
      (semantic /\ operation_originated /\ ! facts_originated))
    (ideal \/
      (semantic /\ operation_originated /\ facts_originated /\
       ! ideal_authorized)).
proof.
  rewrite /origin_partition_holds.
  smt().
qed.

section OriginEnvironmentPartition.
  declare module S <: SIGNATURE_SCHEME.
  declare module H <: NODE_HASH.

  module SO = PG.LoggedSignatureOracle(S).
  module O = OriginTrackedCandidateEnvironment(SO, H).

  lemma origin_sign_operation_preserves_partition :
    hoare [O.sign_operation :
      origin_partition_holds
        O.unauthorized_accepted
        O.bad_operation_signature
        O.bad_fact_signature
        O.ideal_unauthorized
      ==>
      origin_partition_holds
        O.unauthorized_accepted
        O.bad_operation_signature
        O.bad_fact_signature
        O.ideal_unauthorized].
  proof.
    proc.
    if; first by call (_ : true ==> true); auto.
    auto.
  qed.

  lemma origin_sign_fact_preserves_partition :
    hoare [O.sign_authorization_fact :
      origin_partition_holds
        O.unauthorized_accepted
        O.bad_operation_signature
        O.bad_fact_signature
        O.ideal_unauthorized
      ==>
      origin_partition_holds
        O.unauthorized_accepted
        O.bad_operation_signature
        O.bad_fact_signature
        O.ideal_unauthorized].
  proof.
    proc.
    if; first by call (_ : true ==> true); auto.
    auto.
  qed.

  lemma origin_submit_preserves_partition :
    hoare [O.submit :
      origin_partition_holds
        O.unauthorized_accepted
        O.bad_operation_signature
        O.bad_fact_signature
        O.ideal_unauthorized
      ==>
      origin_partition_holds
        O.unauthorized_accepted
        O.bad_operation_signature
        O.bad_fact_signature
        O.ideal_unauthorized].
  proof.
    proc.
    call (_ : true ==> true).
    if.
    + call (_ : true ==> true).
      while
        (origin_partition_holds
          O.unauthorized_accepted
          O.bad_operation_signature
          O.bad_fact_signature
          O.ideal_unauthorized).
      + auto.
      + auto=> />.
        apply origin_partition_update.
        * assumption.
        * move=> semantic.
          have partition := origin_unauthorized_implies_bad_or_ideal
            operation envelope view state_before sign_queries semantic.
          smt().
    + auto.
  qed.
end section OriginEnvironmentPartition.

(* A5 is proved for the same origin-aware adversary interface as A0.  The
   signing procedures cannot affect the ideal flag, while every accepted
   submission inherits the public validator's checked ideal-authorization
   postcondition from the exact pre-state. *)
section OriginIdealInvariant.
  declare module S <: SIGNATURE_SCHEME.
  declare module H <: NODE_HASH.

  module SOI = PG.LoggedSignatureOracle(S).
  module OI = OriginTrackedCandidateEnvironment(SOI, H).

  lemma origin_sign_operation_preserves_no_ideal :
    hoare [OI.sign_operation :
      ! OI.ideal_unauthorized ==> ! OI.ideal_unauthorized].
  proof.
    proc.
    if; first by call (_ : true ==> true); auto.
    auto.
  qed.

  lemma origin_sign_fact_preserves_no_ideal :
    hoare [OI.sign_authorization_fact :
      ! OI.ideal_unauthorized ==> ! OI.ideal_unauthorized].
  proof.
    proc.
    if; first by call (_ : true ==> true); auto.
    auto.
  qed.

  lemma origin_submit_preserves_no_ideal :
    hoare [OI.submit :
      ! OI.ideal_unauthorized ==> ! OI.ideal_unauthorized].
  proof.
    proc.
    call (candidate_submit_acceptance_implies_ideal_authorization
      operation view state_before).
    if.
    + call (_ : true ==> true).
      while (! OI.ideal_unauthorized); first by auto.
      auto=> />.
      rewrite /ideal_authorized_candidate.
      smt().
    + auto.
  qed.
end section OriginIdealInvariant.

type origin_partition_result = {
  opr_real : bool;
  opr_bad_operation : bool;
  opr_bad_fact : bool;
  opr_ideal : bool
}.

module UnauthorizedOriginPartitionGame(
  A : ADAPTIVE_ORIGIN_UNAUTHORIZED_ADVERSARY,
  S : SIGNATURE_SCHEME,
  H : NODE_HASH
) = {
  module SO = PG.LoggedSignatureOracle(S)
  module O = OriginTrackedCandidateEnvironment(SO, H)
  module A = A(O)

  proc main(initial_state : protocol_state) : origin_partition_result = {
    SO.init();
    O.init(initial_state);
    A.attack();
    return
      {| opr_real = O.unauthorized_accepted;
         opr_bad_operation = O.bad_operation_signature;
         opr_bad_fact = O.bad_fact_signature;
         opr_ideal = O.ideal_unauthorized |};
  }
}.

section AdaptiveOriginPartition.
  declare module A <: ADAPTIVE_ORIGIN_UNAUTHORIZED_ADVERSARY.
  declare module S <: SIGNATURE_SCHEME.
  declare module H <: NODE_HASH.

  module G = UnauthorizedOriginPartitionGame(A, S, H).

  lemma origin_adaptive_main_partition
      (initial : protocol_state) :
    hoare [G.main :
      initial_state = initial ==>
      origin_partition_holds
        res.`opr_real
        res.`opr_bad_operation
        res.`opr_bad_fact
        res.`opr_ideal].
  proof.
    proc.
    call (_ :
      origin_partition_holds
        G.O.unauthorized_accepted
        G.O.bad_operation_signature
        G.O.bad_fact_signature
        G.O.ideal_unauthorized).
    + exact origin_sign_operation_preserves_partition.
    + exact origin_sign_fact_preserves_partition.
    + exact origin_submit_preserves_partition.
    auto; rewrite /origin_partition_holds.
  qed.
end section AdaptiveOriginPartition.

section AdaptiveOriginIdealZero.
  declare module A <: ADAPTIVE_ORIGIN_UNAUTHORIZED_ADVERSARY.
  declare module S <: SIGNATURE_SCHEME.
  declare module H <: NODE_HASH.

  module GZ = UnauthorizedOriginPartitionGame(A, S, H).

  lemma origin_adaptive_main_never_ideal
      (initial : protocol_state) :
    hoare [GZ.main :
      initial_state = initial ==> ! res.`opr_ideal].
  proof.
    proc.
    call (_ : ! GZ.O.ideal_unauthorized).
    + exact origin_sign_operation_preserves_no_ideal.
    + exact origin_sign_fact_preserves_no_ideal.
    + exact origin_submit_preserves_no_ideal.
    auto.
  qed.

  lemma origin_ideal_probability_zero
      &m (initial : protocol_state) :
    Pr[
      GZ.main(initial) @ &m : res.`opr_ideal
    ] = 0%r.
  proof.
    byphoare (_ : initial_state = initial ==> ! res.`opr_ideal) => //=.
    exact (origin_adaptive_main_never_ideal initial).
  qed.
end section AdaptiveOriginIdealZero.
