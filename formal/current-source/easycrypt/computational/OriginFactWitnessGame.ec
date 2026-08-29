require import AllCore List FSet.
require import ProtocolTypes CanonicalEncoding ProtocolPrimitives AuthorizationState.
require import ProtocolChecks ProtocolOracles UnauthorizedReduction UnauthorizedSignatureReduction UnauthorizedOriginGame.
require import OriginOperationForgeryPreservation OriginFactSelection OriginFactBadStep.

import PG.

pred fact_forgery_witness_invariant
    (real bad : bool)
    (forgery : PG.signature_forgery option)
    (sign_queries : PG.signature_query list)
    (verify_queries : PG.signature_verification_query list) =
     (bad <=> forgery <> None)
  /\ (bad =>
         real
      /\ PG.signature_forgery_valid
           (oget forgery) sign_queries verify_queries).

(* The wrapper exposes exactly the origin-aware A0 oracle.  Its additional
   field is ghost state unavailable to the adversary and retains the first
   concrete authorization-fact forgery from the exact accepted view. *)
module OriginFactWitnessEnvironment(
  SO : PG.LOGGED_SIGNATURE_ORACLE,
  H : NODE_HASH
) = {
  module Base = OriginTrackedCandidateEnvironment(SO, H)

  var fact_forgery : PG.signature_forgery option

  proc init(initial_state : protocol_state) : unit = {
    Base.init(initial_state);
    fact_forgery <- None;
  }

  proc sign_operation(
    envelope : operation_envelope
  ) : signed_operation = {
    var operation : signed_operation;
    operation <@ Base.sign_operation(envelope);
    return operation;
  }

  proc sign_authorization_fact(
    fact : authorization_fact
  ) : signed_authorization_fact = {
    var signed_fact : signed_authorization_fact;
    signed_fact <@ Base.sign_authorization_fact(fact);
    return signed_fact;
  }

  proc submit(
    operation : signed_operation,
    view : public_view
  ) : bool = {
    var accepted : bool;
    var sign_queries : PG.signature_query list;

    sign_queries <- [];
    if (Base.bad_fact_signature) {
      accepted <@ Base.submit(operation, view);
    } else {
      accepted <@ Base.submit(operation, view);
      if (Base.bad_fact_signature) {
        sign_queries <@ SO.get_sign_queries();
        fact_forgery <- first_unoriginated_fact_forgery
          view.`pv_facts sign_queries;
      }
    }

    return accepted;
  }
}.

section FactWitnessEnvironmentInvariant.
  declare module S <: SIGNATURE_SCHEME.
  declare module H <: NODE_HASH.

  module SO = PG.LoggedSignatureOracle(S).
  module W = OriginFactWitnessEnvironment(SO, H).

  lemma fact_witness_init_establishes_invariant
      (initial : protocol_state) :
    hoare [W.init :
      initial_state = initial ==>
      fact_forgery_witness_invariant
        W.Base.unauthorized_accepted
        W.Base.bad_fact_signature
        W.fact_forgery
        SO.sign_queries SO.verify_queries].
  proof.
    rewrite /fact_forgery_witness_invariant.
    proc.
    inline *.
    auto.
  qed.

  lemma fact_witness_sign_operation_preserves_invariant :
    hoare [W.sign_operation :
      fact_forgery_witness_invariant
        W.Base.unauthorized_accepted
        W.Base.bad_fact_signature
        W.fact_forgery
        SO.sign_queries SO.verify_queries
      ==>
      fact_forgery_witness_invariant
        W.Base.unauthorized_accepted
        W.Base.bad_fact_signature
        W.fact_forgery
        SO.sign_queries SO.verify_queries].
  proof.
    rewrite /fact_forgery_witness_invariant.
    proc.
    inline W.Base.sign_operation.
    if.
    + call (_ : true ==> true).
      auto.
    + auto.
  qed.

  lemma fact_witness_sign_fact_preserves_invariant :
    hoare [W.sign_authorization_fact :
      fact_forgery_witness_invariant
        W.Base.unauthorized_accepted
        W.Base.bad_fact_signature
        W.fact_forgery
        SO.sign_queries SO.verify_queries
      ==>
      fact_forgery_witness_invariant
        W.Base.unauthorized_accepted
        W.Base.bad_fact_signature
        W.fact_forgery
        SO.sign_queries SO.verify_queries].
  proof.
    rewrite /fact_forgery_witness_invariant.
    proc.
    inline W.Base.sign_authorization_fact.
    if.
    + call (_ : true ==> true).
      auto.
    + auto.
  qed.

  lemma fact_witness_submit_preserves_invariant
      (input_operation : signed_operation)
      (input_view : public_view) :
    hoare [W.submit :
         operation = input_operation
      /\ view = input_view
      /\ fact_forgery_witness_invariant
           W.Base.unauthorized_accepted
           W.Base.bad_fact_signature
           W.fact_forgery
           SO.sign_queries SO.verify_queries
      ==>
      fact_forgery_witness_invariant
        W.Base.unauthorized_accepted
        W.Base.bad_fact_signature
        W.fact_forgery
        SO.sign_queries SO.verify_queries].
  proof.
    rewrite /fact_forgery_witness_invariant.
    proc.
    if.
    + call (origin_submit_preserves_bad_real_and_forgery
        (oget W.fact_forgery)).
      auto.
    + call (origin_submit_first_bad_fact_is_valid_forgery
        input_operation input_view).
      if.
      * inline SO.get_sign_queries.
        auto.
      * auto.
  qed.
end section FactWitnessEnvironmentInvariant.

module UnauthorizedOriginFactWitnessGame(
  A : ADAPTIVE_ORIGIN_UNAUTHORIZED_ADVERSARY,
  S : SIGNATURE_SCHEME,
  H : NODE_HASH
) = {
  module SO = PG.LoggedSignatureOracle(S)
  module O = OriginFactWitnessEnvironment(SO, H)
  module A = A(O)

  proc main(initial_state : protocol_state) : bool = {
    SO.init();
    O.init(initial_state);
    A.attack();
    return O.Base.bad_fact_signature;
  }
}.

section AdaptiveFactWitness.
  declare module A <: ADAPTIVE_ORIGIN_UNAUTHORIZED_ADVERSARY.
  declare module S <: SIGNATURE_SCHEME.
  declare module H <: NODE_HASH.

  module G = UnauthorizedOriginFactWitnessGame(A, S, H).

  lemma origin_fact_adaptive_main_witness
      (initial : protocol_state) :
    hoare [G.main :
      initial_state = initial ==>
      fact_forgery_witness_invariant
        G.O.Base.unauthorized_accepted
        res
        G.O.fact_forgery
        G.SO.sign_queries G.SO.verify_queries].
  proof.
    proc.
    call (_ :
      fact_forgery_witness_invariant
        G.O.Base.unauthorized_accepted
        G.O.Base.bad_fact_signature
        G.O.fact_forgery
        G.SO.sign_queries G.SO.verify_queries).
    + exact fact_witness_sign_operation_preserves_invariant.
    + exact fact_witness_sign_fact_preserves_invariant.
    + move=> input_operation input_view.
      exact (fact_witness_submit_preserves_invariant
        input_operation input_view).
    inline G.O.init G.O.Base.init G.O.Base.Base.init G.SO.init.
    auto; rewrite /fact_forgery_witness_invariant.
  qed.

  lemma origin_fact_adaptive_main_characterization
      (initial : protocol_state) :
    hoare [G.main :
      initial_state = initial ==>
      res =
        (G.O.fact_forgery <> None /\
         PG.signature_forgery_valid
           (oget G.O.fact_forgery)
           G.SO.sign_queries G.SO.verify_queries)].
  proof.
    proc.
    call (_ :
      fact_forgery_witness_invariant
        G.O.Base.unauthorized_accepted
        G.O.Base.bad_fact_signature
        G.O.fact_forgery
        G.SO.sign_queries G.SO.verify_queries).
    + exact fact_witness_sign_operation_preserves_invariant.
    + exact fact_witness_sign_fact_preserves_invariant.
    + move=> input_operation input_view.
      exact (fact_witness_submit_preserves_invariant
        input_operation input_view).
    inline G.O.init G.O.Base.init G.O.Base.Base.init G.SO.init.
    auto; rewrite /fact_forgery_witness_invariant; smt().
  qed.
end section AdaptiveFactWitness.

module BSignOriginFactWitness(
  A : ADAPTIVE_ORIGIN_UNAUTHORIZED_ADVERSARY,
  H : NODE_HASH
)(SO : PG.LOGGED_SIGNATURE_ORACLE) = {
  module O = OriginFactWitnessEnvironment(SO, H)
  module A = A(O)

  proc forge(initial_state : protocol_state) : PG.signature_forgery option = {
    O.init(initial_state);
    A.attack();
    return O.fact_forgery;
  }
}.
