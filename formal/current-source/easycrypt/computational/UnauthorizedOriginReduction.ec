require import AllCore List FSet.
require import ProtocolTypes CanonicalEncoding ProtocolPrimitives AuthorizationState.
require import UnauthorizedOriginGame UnauthorizedFactReduction.

import PG.

(* A2 evidence and the primitive reduction execute the same adversary against
   the same origin-aware environment and the same logged primitive oracle. *)
module UnauthorizedOriginA2Evidence(
  A : ADAPTIVE_ORIGIN_UNAUTHORIZED_ADVERSARY,
  S : SIGNATURE_SCHEME,
  H : NODE_HASH
) = {
  module SO = PG.LoggedSignatureOracle(S)
  module O = OriginTrackedCandidateEnvironment(SO, H)
  module A = A(O)

  proc main(initial_state : protocol_state) : bool * bool = {
    var sign_queries : PG.signature_query list;
    var verify_queries : PG.signature_verification_query list;
    var forgery : PG.signature_forgery option;

    SO.init();
    O.init(initial_state);
    A.attack();
    sign_queries <@ SO.get_sign_queries();
    verify_queries <@ SO.get_verify_queries();
    forgery <- find_operation_signature_forgery
      O.accepted_operation_signatures sign_queries verify_queries;

    return (O.unauthorized_accepted, forgery <> None);
  }
}.

module BSignOrigin(
  A : ADAPTIVE_ORIGIN_UNAUTHORIZED_ADVERSARY,
  H : NODE_HASH
)(SO : PG.LOGGED_SIGNATURE_ORACLE) = {
  module O = OriginTrackedCandidateEnvironment(SO, H)
  module A = A(O)

  proc forge(initial_state : protocol_state) : PG.signature_forgery option = {
    var sign_queries : PG.signature_query list;
    var verify_queries : PG.signature_verification_query list;
    var forgery : PG.signature_forgery option;

    O.init(initial_state);
    A.attack();
    sign_queries <@ SO.get_sign_queries();
    verify_queries <@ SO.get_verify_queries();
    forgery <- find_operation_signature_forgery
      O.accepted_operation_signatures sign_queries verify_queries;
    return forgery;
  }
}.

section OriginA2ExactReduction.
  declare module A <: ADAPTIVE_ORIGIN_UNAUTHORIZED_ADVERSARY.
  declare module S <: SIGNATURE_SCHEME.
  declare module H <: NODE_HASH.

  lemma origin_bad_operation_signature_exactly_reduces_to_multi_user_eufcma
      &m initial_state :
    Pr[
      UnauthorizedOriginA2Evidence(A, S, H).main(initial_state) @ &m :
      res.`2
    ] =
    Pr[
      PG.MultiUserEUFCMAGame(BSignOrigin(A, H), S).main(initial_state) @ &m :
      res
    ].
  proof.
    byequiv
      (_ : ={initial_state, glob A, glob S, glob H} ==>
           res{1}.`2 = res{2}) => //.
    proc.
    inline *.
    sim.
  qed.
end section OriginA2ExactReduction.

(* The authorization-fact reduction traverses every accepted causal view.  A
   candidate is fresh exactly when its issuer/message pair was absent from the
   same primitive sign log that backed validator verification. *)
module UnauthorizedOriginA3Evidence(
  A : ADAPTIVE_ORIGIN_UNAUTHORIZED_ADVERSARY,
  S : SIGNATURE_SCHEME,
  H : NODE_HASH
) = {
  module SO = PG.LoggedSignatureOracle(S)
  module O = OriginTrackedCandidateEnvironment(SO, H)
  module A = A(O)

  proc main(initial_state : protocol_state) : bool * bool = {
    var sign_queries : PG.signature_query list;
    var verify_queries : PG.signature_verification_query list;
    var forgery : PG.signature_forgery option;

    SO.init();
    O.init(initial_state);
    A.attack();
    sign_queries <@ SO.get_sign_queries();
    verify_queries <@ SO.get_verify_queries();
    forgery <- find_fact_signature_forgery
      O.accepted_fact_signatures sign_queries verify_queries;

    return (O.unauthorized_accepted, forgery <> None);
  }
}.

module BSignFactsOrigin(
  A : ADAPTIVE_ORIGIN_UNAUTHORIZED_ADVERSARY,
  H : NODE_HASH
)(SO : PG.LOGGED_SIGNATURE_ORACLE) = {
  module O = OriginTrackedCandidateEnvironment(SO, H)
  module A = A(O)

  proc forge(initial_state : protocol_state) : PG.signature_forgery option = {
    var sign_queries : PG.signature_query list;
    var verify_queries : PG.signature_verification_query list;
    var forgery : PG.signature_forgery option;

    O.init(initial_state);
    A.attack();
    sign_queries <@ SO.get_sign_queries();
    verify_queries <@ SO.get_verify_queries();
    forgery <- find_fact_signature_forgery
      O.accepted_fact_signatures sign_queries verify_queries;
    return forgery;
  }
}.

section OriginA3ExactReduction.
  declare module A <: ADAPTIVE_ORIGIN_UNAUTHORIZED_ADVERSARY.
  declare module S <: SIGNATURE_SCHEME.
  declare module H <: NODE_HASH.

  lemma origin_bad_fact_signature_exactly_reduces_to_multi_user_eufcma
      &m initial_state :
    Pr[
      UnauthorizedOriginA3Evidence(A, S, H).main(initial_state) @ &m :
      res.`2
    ] =
    Pr[
      PG.MultiUserEUFCMAGame(BSignFactsOrigin(A, H), S).main(initial_state) @ &m :
      res
    ].
  proof.
    byequiv
      (_ : ={initial_state, glob A, glob S, glob H} ==>
           res{1}.`2 = res{2}) => //.
    proc.
    inline *.
    sim.
  qed.
end section OriginA3ExactReduction.
