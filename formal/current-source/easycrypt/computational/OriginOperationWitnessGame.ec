require import AllCore List FSet.
require import ProtocolTypes CanonicalEncoding ProtocolPrimitives AuthorizationState.
require import ProtocolChecks ProtocolOracles UnauthorizedReduction UnauthorizedSignatureReduction UnauthorizedOriginGame.
require import OriginOperationVerificationEvidence OriginOperationForgeryPreservation OriginOperationBadStep.

import PG.

pred operation_forgery_witness_invariant
    (real bad : bool)
    (forgery : PG.signature_forgery option)
    (sign_queries : PG.signature_query list)
    (verify_queries : PG.signature_verification_query list) =
     (bad <=> forgery <> None)
  /\ (bad =>
         real
      /\ PG.signature_forgery_valid
           (oget forgery) sign_queries verify_queries).

(* This wrapper exposes exactly the protocol-shaped A0 oracle.  The extra
   witness is ghost state: the adversary cannot read it, and every public
   operation delegates to the origin-aware production environment unchanged. *)
module OriginOperationWitnessEnvironment(
  SO : PG.LOGGED_SIGNATURE_ORACLE,
  H : NODE_HASH
) = {
  module Base = OriginTrackedCandidateEnvironment(SO, H)

  var operation_forgery : PG.signature_forgery option

  proc init(initial_state : protocol_state) : unit = {
    Base.init(initial_state);
    operation_forgery <- None;
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

    if (Base.bad_operation_signature) {
      accepted <@ Base.submit(operation, view);
    } else {
      accepted <@ Base.submit(operation, view);
      if (Base.bad_operation_signature) {
        operation_forgery <- Some
          (operation_signature_forgery_candidate
            operation (oget (decode_operation operation.`so_raw)));
      }
    }

    return accepted;
  }
}.

section OperationWitnessEnvironmentInvariant.
  declare module S <: SIGNATURE_SCHEME.
  declare module H <: NODE_HASH.

  module SO = PG.LoggedSignatureOracle(S).
  module W = OriginOperationWitnessEnvironment(SO, H).

  lemma operation_witness_init_establishes_invariant
      (initial : protocol_state) :
    hoare [W.init :
      initial_state = initial ==>
      operation_forgery_witness_invariant
        W.Base.unauthorized_accepted
        W.Base.bad_operation_signature
        W.operation_forgery
        SO.sign_queries SO.verify_queries].
  proof.
    rewrite /operation_forgery_witness_invariant.
    proc.
    inline *.
    auto.
  qed.

  lemma operation_witness_sign_operation_preserves_invariant :
    hoare [W.sign_operation :
      operation_forgery_witness_invariant
        W.Base.unauthorized_accepted
        W.Base.bad_operation_signature
        W.operation_forgery
        SO.sign_queries SO.verify_queries
      ==>
      operation_forgery_witness_invariant
        W.Base.unauthorized_accepted
        W.Base.bad_operation_signature
        W.operation_forgery
        SO.sign_queries SO.verify_queries].
  proof.
    rewrite /operation_forgery_witness_invariant.
    proc.
    inline W.Base.sign_operation.
    if.
    + call (_ : true ==> true).
      auto.
    + auto.
  qed.

  lemma operation_witness_sign_fact_preserves_invariant :
    hoare [W.sign_authorization_fact :
      operation_forgery_witness_invariant
        W.Base.unauthorized_accepted
        W.Base.bad_operation_signature
        W.operation_forgery
        SO.sign_queries SO.verify_queries
      ==>
      operation_forgery_witness_invariant
        W.Base.unauthorized_accepted
        W.Base.bad_operation_signature
        W.operation_forgery
        SO.sign_queries SO.verify_queries].
  proof.
    rewrite /operation_forgery_witness_invariant.
    proc.
    inline W.Base.sign_authorization_fact.
    if.
    + call (_ : true ==> true).
      auto.
    + auto.
  qed.

  lemma operation_witness_submit_preserves_invariant
      (input_operation : signed_operation)
      (input_view : public_view) :
    hoare [W.submit :
         operation = input_operation
      /\ view = input_view
      /\ operation_forgery_witness_invariant
           W.Base.unauthorized_accepted
           W.Base.bad_operation_signature
           W.operation_forgery
           SO.sign_queries SO.verify_queries
      ==>
      operation_forgery_witness_invariant
        W.Base.unauthorized_accepted
        W.Base.bad_operation_signature
        W.operation_forgery
        SO.sign_queries SO.verify_queries].
  proof.
    rewrite /operation_forgery_witness_invariant.
    proc.
    if.
    + call (origin_submit_preserves_bad_real_and_forgery
        (oget W.operation_forgery)).
      auto.
    + call (origin_submit_first_bad_operation_is_valid_forgery
        input_operation input_view).
      if; auto.
  qed.
end section OperationWitnessEnvironmentInvariant.

module UnauthorizedOriginOperationWitnessGame(
  A : ADAPTIVE_ORIGIN_UNAUTHORIZED_ADVERSARY,
  S : SIGNATURE_SCHEME,
  H : NODE_HASH
) = {
  module SO = PG.LoggedSignatureOracle(S)
  module O = OriginOperationWitnessEnvironment(SO, H)
  module A = A(O)

  proc main(initial_state : protocol_state) : bool = {
    SO.init();
    O.init(initial_state);
    A.attack();
    return O.Base.bad_operation_signature;
  }
}.

section AdaptiveOperationWitnessInvariant.
  declare module A <: ADAPTIVE_ORIGIN_UNAUTHORIZED_ADVERSARY.
  declare module S <: SIGNATURE_SCHEME.
  declare module H <: NODE_HASH.

  module G = UnauthorizedOriginOperationWitnessGame(A, S, H).

  lemma operation_witness_adaptive_main_invariant
      (initial : protocol_state) :
    hoare [G.main :
      initial_state = initial ==>
      operation_forgery_witness_invariant
        G.O.Base.unauthorized_accepted
        G.O.Base.bad_operation_signature
        G.O.operation_forgery
        G.SO.sign_queries G.SO.verify_queries].
  proof.
    proc.
    call (_ :
      operation_forgery_witness_invariant
        G.O.Base.unauthorized_accepted
        G.O.Base.bad_operation_signature
        G.O.operation_forgery
        G.SO.sign_queries G.SO.verify_queries).
    + exact operation_witness_sign_operation_preserves_invariant.
    + exact operation_witness_sign_fact_preserves_invariant.
    + move=> input_operation input_view.
      exact (operation_witness_submit_preserves_invariant
        input_operation input_view).
    inline G.O.init G.O.Base.init G.O.Base.Base.init G.SO.init.
    auto; rewrite /operation_forgery_witness_invariant.
  qed.

  (* The actual adaptive A2 bad flag is exactly the primitive-game success
     predicate for the retained first forgery.  In particular, [None] cannot
     witness a bad event, and a retained [Some] value cannot be spurious. *)
  lemma operation_witness_adaptive_main_characterization
      (initial : protocol_state) :
    hoare [G.main :
      initial_state = initial ==>
      res =
        (G.O.operation_forgery <> None /\
         PG.signature_forgery_valid
           (oget G.O.operation_forgery)
           G.SO.sign_queries G.SO.verify_queries)].
  proof.
    proc.
    call (_ :
      operation_forgery_witness_invariant
        G.O.Base.unauthorized_accepted
        G.O.Base.bad_operation_signature
        G.O.operation_forgery
        G.SO.sign_queries G.SO.verify_queries).
    + exact operation_witness_sign_operation_preserves_invariant.
    + exact operation_witness_sign_fact_preserves_invariant.
    + move=> input_operation input_view.
      exact (operation_witness_submit_preserves_invariant
        input_operation input_view).
    inline G.O.init G.O.Base.init G.O.Base.Base.init G.SO.init.
    auto; rewrite /operation_forgery_witness_invariant; smt().
  qed.
end section AdaptiveOperationWitnessInvariant.

(* The reduction adversary returns the retained first operation forgery from
   the same adaptive execution that sets the A2 bad flag.  The primitive game,
   not the reduction, rechecks the candidate against the exact sign and verify
   logs after the attack. *)
module BSignOriginOperationWitness(
  A : ADAPTIVE_ORIGIN_UNAUTHORIZED_ADVERSARY,
  H : NODE_HASH
)(SO : PG.LOGGED_SIGNATURE_ORACLE) = {
  module O = OriginOperationWitnessEnvironment(SO, H)
  module A = A(O)

  proc forge(initial_state : protocol_state) : PG.signature_forgery option = {
    O.init(initial_state);
    A.attack();
    return O.operation_forgery;
  }
}.
