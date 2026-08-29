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

  pred origin_environment_partition =
    origin_partition_holds
      O.unauthorized_accepted
      O.bad_operation_signature
      O.bad_fact_signature
      O.ideal_unauthorized.

  lemma origin_sign_operation_preserves_partition :
    hoare [O.sign_operation :
      origin_environment_partition ==>
      origin_environment_partition].
  proof.
    proc.
    if; first by call (_ : true ==> true); auto.
    auto.
  qed.

  lemma origin_sign_fact_preserves_partition :
    hoare [O.sign_authorization_fact :
      origin_environment_partition ==>
      origin_environment_partition].
  proof.
    proc.
    if; first by call (_ : true ==> true); auto.
    auto.
  qed.

  lemma origin_submit_preserves_partition :
    hoare [O.submit :
      origin_environment_partition ==>
      origin_environment_partition].
  proof.
    proc.
    call (_ : true ==> true).
    if.
    + call (_ : true ==> true).
      while (origin_environment_partition).
      + auto.
      + auto=> />.
        rewrite /origin_environment_partition.
        apply origin_partition_update.
        * assumption.
        * move=> semantic.
          have partition := origin_unauthorized_implies_bad_or_ideal
            operation envelope view state_before sign_queries semantic.
          smt().
    + auto.
  qed.
end section OriginEnvironmentPartition.
