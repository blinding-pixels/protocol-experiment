require import AllCore List FSet.
require import ProtocolTypes CanonicalEncoding ProtocolPrimitives AuthorizationState.
require import ProtocolChecks ProtocolOracles AuthorizationAncestry UnauthorizedReduction UnauthorizedIdeal.
require import UnauthorizedSignatureReduction.

import PG.

(* Signing origin is a fact about the executable primitive oracle transcript,
   never an adversary-supplied Boolean.  Operation and authorization signing
   APIs below force the verification key and message to be the exact protocol
   values embedded in the object being signed. *)
op operation_signature_originated
    (operation : signed_operation)
    (envelope : operation_envelope)
    (sign_queries : PG.signature_query list) : bool =
     operation.`so_signature.`sig_verification_key =
       envelope.`oe_author.`p_verification_key
  /\ mem sign_queries
       (envelope.`oe_author.`p_verification_key,
        operation_signature_message Production envelope).

op fact_signature_originated
    (signed_fact : signed_authorization_fact)
    (sign_queries : PG.signature_query list) : bool =
     signed_fact.`saf_signature.`sig_verification_key =
       signed_fact.`saf_fact.`af_issuer.`p_verification_key
  /\ mem sign_queries
       (signed_fact.`saf_fact.`af_issuer.`p_verification_key,
        fact_signature_message signed_fact.`saf_fact).

op all_fact_signatures_originated
    (facts : signed_authorization_fact list)
    (sign_queries : PG.signature_query list) : bool =
  with facts = [] => true
  with facts = signed_fact :: rest =>
       fact_signature_originated signed_fact sign_queries
    /\ all_fact_signatures_originated rest sign_queries.

op originated_signed_facts
    (facts : signed_authorization_fact list)
    (sign_queries : PG.signature_query list) :
    signed_authorization_fact list =
  with facts = [] => []
  with facts = signed_fact :: rest =>
    if fact_signature_originated signed_fact sign_queries
    then signed_fact :: originated_signed_facts rest sign_queries
    else originated_signed_facts rest sign_queries.

lemma all_originated_filter_identity
    (facts : signed_authorization_fact list)
    (sign_queries : PG.signature_query list) :
  all_fact_signatures_originated facts sign_queries =>
  originated_signed_facts facts sign_queries = facts.
proof.
  elim: facts => [| signed_fact rest ih] //=.
  move=> [originated rest_originated].
  by rewrite originated (ih rest_originated).
qed.

op authenticated_authorization_state
    (view : public_view)
    (state : protocol_state)
    (sign_queries : PG.signature_query list) : authorization_state option =
  authorization_policy_replay
    state.`ps_creator
    (originated_signed_facts view.`pv_facts sign_queries).

(* This is A0's semantic event after the production validator accepts.  The
   operation signature must originate from the correct protocol signing query,
   while membership and capability are evaluated in the policy replay of only
   origin-authenticated facts from the exact accepted causal view. *)
op origin_unauthorized_acceptance_condition
    (operation : signed_operation)
    (envelope : operation_envelope)
    (view : public_view)
    (state : protocol_state)
    (sign_queries : PG.signature_query list) : bool =
  let authenticated =
    authenticated_authorization_state view state sign_queries in
     ! operation_signature_originated operation envelope sign_queries
  \/ authenticated = None
  \/ ! member_active Production (oget authenticated) envelope.`oe_author
  \/ ! capability_active Production (oget authenticated)
       envelope.`oe_author envelope.`oe_required_capability
  \/ envelope.`oe_required_capability <>
       required_capability_for_operation
         envelope.`oe_operation_kind envelope.`oe_operation_body
  \/ ! operation_body_valid_for_envelope envelope.

(* If every accepted signature has origin, authenticated replay is the A5
   replay over the complete exact view.  Hence a real unauthorized event must
   expose an operation forgery, a fact forgery, or an A5 ideal violation. *)
lemma origin_unauthorized_implies_bad_or_ideal
    (operation : signed_operation)
    (envelope : operation_envelope)
    (view : public_view)
    (state : protocol_state)
    (sign_queries : PG.signature_query list) :
  origin_unauthorized_acceptance_condition
    operation envelope view state sign_queries =>
     ! operation_signature_originated operation envelope sign_queries
  \/ ! all_fact_signatures_originated view.`pv_facts sign_queries
  \/ ! ideal_decoded_authorized operation envelope view state.
proof.
  move=> unauthorized.
  case (operation_signature_originated
          operation envelope sign_queries) => operation_originated.
  + case (all_fact_signatures_originated
            view.`pv_facts sign_queries) => facts_originated.
    + right; right.
      apply contraT => ideal.
      rewrite /origin_unauthorized_acceptance_condition
        /authenticated_authorization_state
        (all_originated_filter_identity
          view.`pv_facts sign_queries facts_originated)
        /ideal_authorization_state in unauthorized.
      rewrite /ideal_decoded_authorized in ideal.
      smt().
    + by right; left.
  + by left.
qed.

module type ORIGIN_TRACKED_UNAUTHORIZED_ORACLE = {
  proc sign_operation(envelope : operation_envelope) : signed_operation
  proc sign_authorization_fact(
    fact : authorization_fact
  ) : signed_authorization_fact
  proc submit(operation : signed_operation, view : public_view) : bool
}.

module type ADAPTIVE_ORIGIN_UNAUTHORIZED_ADVERSARY(
  O : ORIGIN_TRACKED_UNAUTHORIZED_ORACLE
) = {
  proc attack() : unit
}.

(* One shared logged signature oracle backs protocol signing, fact verification,
   and operation verification.  The adversary receives protocol-shaped signing
   procedures rather than the raw (key,message) primitive interface. *)
module OriginTrackedCandidateEnvironment(
  SO : PG.LOGGED_SIGNATURE_ORACLE,
  H : NODE_HASH
) = {
  module Scheme = PG.SignatureOracleScheme(SO)
  module Base = CandidateUnauthorizedEnvironment(Scheme, H)

  var accepted_operation_signatures : PG.signature_forgery list
  var accepted_fact_signatures : PG.signature_forgery list
  var bad_operation_signature : bool
  var bad_fact_signature : bool
  var ideal_unauthorized : bool
  var unauthorized_accepted : bool

  proc init(initial_state : protocol_state) : unit = {
    Base.init(initial_state);
    accepted_operation_signatures <- [];
    accepted_fact_signatures <- [];
    bad_operation_signature <- false;
    bad_fact_signature <- false;
    ideal_unauthorized <- false;
    unauthorized_accepted <- false;
  }

  (* Once the real win event has occurred, the game is closed.  Refusing later
     signing queries prevents an adversary from laundering a recorded forgery
     by asking for its exact message after the winning submission. *)
  proc sign_operation(envelope : operation_envelope) : signed_operation = {
    var sig : signature;
    sig <- witness;
    if (! unauthorized_accepted) {
      sig <@ SO.sign(
        envelope.`oe_author.`p_verification_key,
        operation_signature_message Production envelope
      );
    }
    return
      {| so_raw = encode_operation envelope;
         so_signature = sig |};
  }

  proc sign_authorization_fact(
    fact : authorization_fact
  ) : signed_authorization_fact = {
    var sig : signature;
    sig <- witness;
    if (! unauthorized_accepted) {
      sig <@ SO.sign(
        fact.`af_issuer.`p_verification_key,
        fact_signature_message fact
      );
    }
    return {| saf_fact = fact; saf_signature = sig |};
  }

  proc submit(
    operation : signed_operation,
    view : public_view
  ) : bool = {
    var state_before : protocol_state;
    var accepted : bool;
    var envelope : operation_envelope;
    var sign_queries : PG.signature_query list;
    var remaining : signed_authorization_fact list;
    var signed_fact : signed_authorization_fact;
    var operation_candidate : PG.signature_forgery;
    var fact_candidate : PG.signature_forgery;
    var operation_originated : bool;
    var facts_originated : bool;
    var semantic_unauthorized : bool;

    state_before <- Base.state;
    accepted <@ Base.submit(operation, view);
    envelope <- witness;
    sign_queries <- [];
    remaining <- [];
    signed_fact <- witness;
    operation_candidate <- witness;
    fact_candidate <- witness;
    operation_originated <- false;
    facts_originated <- false;
    semantic_unauthorized <- false;

    if (accepted) {
      envelope <- oget (decode_operation operation.`so_raw);
      sign_queries <@ SO.get_sign_queries();

      operation_candidate <-
        {| sf_verification_key =
             operation.`so_signature.`sig_verification_key;
           sf_message =
             operation_signature_message Production envelope;
           sf_signature = operation.`so_signature |};
      accepted_operation_signatures <-
        rcons accepted_operation_signatures operation_candidate;

      remaining <- view.`pv_facts;
      while (remaining <> []) {
        signed_fact <- head witness remaining;
        remaining <- behead remaining;
        fact_candidate <-
          {| sf_verification_key =
               signed_fact.`saf_signature.`sig_verification_key;
             sf_message = fact_signature_message signed_fact.`saf_fact;
             sf_signature = signed_fact.`saf_signature |};
        accepted_fact_signatures <-
          rcons accepted_fact_signatures fact_candidate;
      }

      operation_originated <-
        operation_signature_originated operation envelope sign_queries;
      facts_originated <-
        all_fact_signatures_originated view.`pv_facts sign_queries;
      semantic_unauthorized <-
        origin_unauthorized_acceptance_condition
          operation envelope view state_before sign_queries;

      bad_operation_signature <-
        bad_operation_signature \/ ! operation_originated;
      bad_fact_signature <-
        bad_fact_signature \/ ! facts_originated;
      ideal_unauthorized <-
        ideal_unauthorized \/
        ! ideal_decoded_authorized operation envelope view state_before;
      unauthorized_accepted <-
        unauthorized_accepted \/ semantic_unauthorized;
    }

    return accepted;
  }
}.

module UnauthorizedA0OriginReal(
  A : ADAPTIVE_ORIGIN_UNAUTHORIZED_ADVERSARY,
  S : SIGNATURE_SCHEME,
  H : NODE_HASH
) = {
  module SO = PG.LoggedSignatureOracle(S)
  module O = OriginTrackedCandidateEnvironment(SO, H)
  module A = A(O)

  proc main(initial_state : protocol_state) : bool = {
    SO.init();
    O.init(initial_state);
    A.attack();
    return O.unauthorized_accepted;
  }
}.
