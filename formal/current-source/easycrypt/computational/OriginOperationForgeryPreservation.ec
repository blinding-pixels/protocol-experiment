require import AllCore List FSet.
require import ProtocolTypes CanonicalEncoding ProtocolPrimitives AuthorizationState.
require import ProtocolChecks ProtocolOracles UnauthorizedReduction UnauthorizedSignatureReduction UnauthorizedOriginGame.
require import OriginOperationVerificationEvidence.

import PG.

(* A successful primitive verification already present in the log remains
   present when another verification result is appended.  No signing query is
   introduced by this step, so freshness is preserved as well. *)
lemma signature_forgery_valid_after_verify_append
    (candidate : PG.signature_forgery)
    (sign_queries : PG.signature_query list)
    (verify_queries : PG.signature_verification_query list)
    (query : PG.signature_verification_query) :
  PG.signature_forgery_valid candidate sign_queries verify_queries =>
  PG.signature_forgery_valid
    candidate sign_queries (rcons verify_queries query).
proof.
  rewrite /PG.signature_forgery_valid mem_rcons.
  smt().
qed.

section ExistingForgeryPreservation.
  declare module S <: SIGNATURE_SCHEME.
  declare module H <: NODE_HASH.

  module SO = PG.LoggedSignatureOracle(S).
  module Scheme = PG.SignatureOracleScheme(SO).
  module N = NormalizeAuthorization(Scheme).
  module V = ValidateOperation(Scheme).
  module C = CandidateUnauthorizedEnvironment(Scheme, H).

  lemma signature_oracle_scheme_verify_preserves_forgery
      (candidate : PG.signature_forgery) :
    hoare [Scheme.verify :
      PG.signature_forgery_valid
        candidate SO.sign_queries SO.verify_queries
      ==>
      PG.signature_forgery_valid
        candidate SO.sign_queries SO.verify_queries].
  proof.
    proc.
    inline *.
    wp.
    call (_ : true ==> true).
    auto=> />.
    rewrite /PG.signature_forgery_valid mem_rcons.
    smt().
  qed.

  lemma normalize_preserves_existing_forgery
      (candidate : PG.signature_forgery) :
    hoare [N.normalize :
      PG.signature_forgery_valid
        candidate SO.sign_queries SO.verify_queries
      ==>
      PG.signature_forgery_valid
        candidate SO.sign_queries SO.verify_queries].
  proof.
    proc.
    while
      (PG.signature_forgery_valid
        candidate SO.sign_queries SO.verify_queries).
    + wp.
      call (signature_oracle_scheme_verify_preserves_forgery candidate).
      auto.
    + auto.
  qed.

  lemma validate_decoded_preserves_existing_forgery
      (candidate : PG.signature_forgery) :
    hoare [V.validate_decoded :
      PG.signature_forgery_valid
        candidate SO.sign_queries SO.verify_queries
      ==>
      PG.signature_forgery_valid
        candidate SO.sign_queries SO.verify_queries].
  proof.
    proc.
    wp.
    call (signature_oracle_scheme_verify_preserves_forgery candidate).
    wp.
    call (normalize_preserves_existing_forgery candidate).
    auto.
  qed.

  lemma validate_preserves_existing_forgery
      (candidate : PG.signature_forgery) :
    hoare [V.validate :
      PG.signature_forgery_valid
        candidate SO.sign_queries SO.verify_queries
      ==>
      PG.signature_forgery_valid
        candidate SO.sign_queries SO.verify_queries].
  proof.
    proc.
    call (validate_decoded_preserves_existing_forgery candidate).
    auto.
  qed.

  lemma candidate_submit_preserves_existing_forgery
      (candidate : PG.signature_forgery) :
    hoare [C.submit :
      PG.signature_forgery_valid
        candidate SO.sign_queries SO.verify_queries
      ==>
      PG.signature_forgery_valid
        candidate SO.sign_queries SO.verify_queries].
  proof.
    proc.
    wp.
    call (_ : true ==> true).
    call (validate_preserves_existing_forgery candidate).
    auto.
  qed.
end section ExistingForgeryPreservation.
