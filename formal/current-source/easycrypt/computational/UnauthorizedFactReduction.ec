require import AllCore List FSet.
require import ProtocolTypes CanonicalEncoding ProtocolPrimitives AuthorizationState.
require PrimitiveGames.
clone import PrimitiveGames as PG.
require import UnauthorizedSignatureReduction UnauthorizedReduction.

(* Convert the signed authorization facts supplied in an accepted public view
   into the exact primitive-message candidates checked by the shared
   normalizer. *)
op fact_signature_candidate
    (signed_fact : signed_authorization_fact) : PG.signature_forgery =
  {| sf_verification_key =
       signed_fact.`saf_signature.`sig_verification_key;
     sf_message = fact_signature_message signed_fact.`saf_fact;
     sf_signature = signed_fact.`saf_signature |}.

op fact_signature_candidates
    (facts : signed_authorization_fact list) : PG.signature_forgery list =
  with facts = [] => []
  with facts = signed_fact :: rest =>
    fact_signature_candidate signed_fact ::
      fact_signature_candidates rest.

op find_fact_signature_forgery
    (accepted : PG.signature_forgery list)
    (sign_queries : PG.signature_query list)
    (verify_queries : PG.signature_verification_query list) :
    PG.signature_forgery option =
  with accepted = [] => None
  with accepted = candidate :: rest =>
    if PG.signature_forgery_valid candidate sign_queries verify_queries
    then Some candidate
    else find_fact_signature_forgery rest sign_queries verify_queries.

module CandidateFactSignatureEnvironment(
  SO : PG.LOGGED_SIGNATURE_ORACLE,
  H : NODE_HASH
) = {
  module Base = CandidateSignatureEnvironment(SO, H)

  var accepted_fact_signatures : PG.signature_forgery list
  var unauthorized_accepted : bool

  proc init(initial_state : protocol_state) : unit = {
    Base.init(initial_state);
    accepted_fact_signatures <- [];
    unauthorized_accepted <- false;
  }

  proc sign(
    vk : verification_key,
    message : signature_message
  ) : signature = {
    var sig : signature;
    sig <@ Base.sign(vk, message);
    return sig;
  }

  proc submit(
    operation : signed_operation,
    view : public_view
  ) : bool = {
    var accepted : bool;

    accepted <@ Base.submit(operation, view);
    if (accepted) {
      accepted_fact_signatures <-
        accepted_fact_signatures ++ fact_signature_candidates view.`pv_facts;
    }
    unauthorized_accepted <- Base.unauthorized_accepted;
    return accepted;
  }
}.

module UnauthorizedA3FactEvidence(
  A : ADAPTIVE_SIGNED_UNAUTHORIZED_ADVERSARY,
  S : SIGNATURE_SCHEME,
  H : NODE_HASH
) = {
  module SO = PG.LoggedSignatureOracle(S)
  module O = CandidateFactSignatureEnvironment(SO, H)
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

module BSignFacts(
  A : ADAPTIVE_SIGNED_UNAUTHORIZED_ADVERSARY,
  H : NODE_HASH
)(SO : PG.LOGGED_SIGNATURE_ORACLE) = {
  module O = CandidateFactSignatureEnvironment(SO, H)
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

section A3FactSignatureReduction.
  declare module A <: ADAPTIVE_SIGNED_UNAUTHORIZED_ADVERSARY.
  declare module S <: SIGNATURE_SCHEME.
  declare module H <: NODE_HASH.

  lemma bad_fact_signature_exactly_reduces_to_multi_user_eufcma
      &m initial_state :
    Pr[
      UnauthorizedA3FactEvidence(A, S, H).main(initial_state) @ &m :
      res.`2
    ] =
    Pr[
      PG.MultiUserEUFCMAGame(BSignFacts(A, H), S).main(initial_state) @ &m :
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
end section A3FactSignatureReduction.
