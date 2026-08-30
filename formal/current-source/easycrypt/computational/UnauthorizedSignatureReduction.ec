require import AllCore List FSet.
require import ProtocolTypes CanonicalEncoding ProtocolPrimitives.
require PrimitiveGames.
clone import PrimitiveGames as PG.
require import UnauthorizedReduction.

op find_operation_signature_forgery
    (accepted : PG.signature_forgery list)
    (sign_queries : PG.signature_query list)
    (verify_queries : PG.signature_verification_query list) :
    PG.signature_forgery option =
  with accepted = [] => None
  with accepted = candidate :: rest =>
    if PG.signature_forgery_valid candidate sign_queries verify_queries
    then Some candidate
    else find_operation_signature_forgery rest sign_queries verify_queries.

(* The A2 adversary can submit arbitrary public candidates and can request
   honest signatures on arbitrary operation or authorization-fact messages.
   Both procedures are backed by the same logged primitive oracle. *)
module type SIGNED_UNAUTHORIZED_ORACLE = {
  proc submit(
    operation : signed_operation,
    view : public_view
  ) : bool

  proc sign(
    vk : verification_key,
    message : signature_message
  ) : signature
}.

module CandidateSignatureEnvironment(
  SO : PG.LOGGED_SIGNATURE_ORACLE,
  H : NODE_HASH
) = {
  module Scheme = PG.SignatureOracleScheme(SO)
  module Base = CandidateUnauthorizedEnvironment(Scheme, H)

  var accepted_signatures : PG.signature_forgery list
  var unauthorized_accepted : bool

  proc init(initial_state : protocol_state) : unit = {
    Base.init(initial_state);
    accepted_signatures <- [];
    unauthorized_accepted <- false;
  }

  proc sign(
    vk : verification_key,
    message : signature_message
  ) : signature = {
    var sig : signature;
    sig <@ SO.sign(vk, message);
    return sig;
  }

  proc submit(
    operation : signed_operation,
    view : public_view
  ) : bool = {
    var envelope_option : operation_envelope option;
    var envelope : operation_envelope;
    var accepted : bool;
    var candidate : PG.signature_forgery;

    envelope_option <- decode_operation operation.`so_raw;
    envelope <- witness;
    candidate <- witness;
    accepted <@ Base.submit(operation, view);

    if (accepted /\ envelope_option <> None) {
      envelope <- oget envelope_option;
      candidate <-
        {| sf_verification_key =
             operation.`so_signature.`sig_verification_key;
           sf_message =
             operation_signature_message Production envelope;
           sf_signature = operation.`so_signature |};
      accepted_signatures <- rcons accepted_signatures candidate;
    }

    unauthorized_accepted <- Base.unauthorized_accepted;
    return accepted;
  }
}.

module type ADAPTIVE_SIGNED_UNAUTHORIZED_ADVERSARY(
  O : SIGNED_UNAUTHORIZED_ORACLE
) = {
  proc attack() : unit
}.

module UnauthorizedA2SignatureEvidence(
  A : ADAPTIVE_SIGNED_UNAUTHORIZED_ADVERSARY,
  S : SIGNATURE_SCHEME,
  H : NODE_HASH
) = {
  module SO = PG.LoggedSignatureOracle(S)
  module O = CandidateSignatureEnvironment(SO, H)
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
      O.accepted_signatures sign_queries verify_queries;

    return (O.unauthorized_accepted, forgery <> None);
  }
}.

(* Named A2 operation-signature reduction.  Its output is optional so the
   primitive game cannot win through an arbitrary dummy value when no accepted
   unoriginated signature exists. *)
module BSign(
  A : ADAPTIVE_SIGNED_UNAUTHORIZED_ADVERSARY,
  H : NODE_HASH
)(SO : PG.LOGGED_SIGNATURE_ORACLE) = {
  module O = CandidateSignatureEnvironment(SO, H)
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
      O.accepted_signatures sign_queries verify_queries;
    return forgery;
  }
}.

section A2ExactReduction.
  declare module A <: ADAPTIVE_SIGNED_UNAUTHORIZED_ADVERSARY.
  declare module S <: SIGNATURE_SCHEME.
  declare module H <: NODE_HASH.

  lemma bad_operation_signature_exactly_reduces_to_multi_user_eufcma
      &m initial_state :
    Pr[
      UnauthorizedA2SignatureEvidence(A, S, H).main(initial_state) @ &m :
      res.`2
    ] =
    Pr[
      PG.MultiUserEUFCMAGame(BSign(A, H), S).main(initial_state) @ &m :
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
end section A2ExactReduction.
