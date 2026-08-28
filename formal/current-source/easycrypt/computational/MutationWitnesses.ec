require import AllCore List FSet.
require import ProtocolTypes CanonicalEncoding ProtocolPrimitives AuthorizationState.
require import ProtocolChecks ProtocolOracles UnauthorizedGame WitnessFixtures.

op witness_edit_body_one : operation_body =
  EditBody EditText (Payload 1).

op witness_edit_body_two : operation_body =
  EditBody EditText (Payload 2).

op witness_delete_body : operation_body =
  EditBody DeleteDocument (Payload 3).

module StatefulMutationRunner = {
  module D = DifferentialEnvironment(TestSignature, TestNodeHash)

  proc run(
    removed : defense,
    fixture : witness_fixture,
    operation : signed_operation
  ) : bool * int = {
    var accepted : bool;
    D.init(removed, fixture.`wf_state, fixture.`wf_facts);
    accepted <@ D.submit(operation);
    return (D.differential_win, D.query_count);
  }
}.

module DirectMutationRunner = {
  module D = DifferentialValidator(TestSignature)

  proc run(
    removed : defense,
    operation : signed_operation,
    view : public_view,
    state : protocol_state
  ) : bool * int = {
    var accepted : bool;
    D.init(removed);
    accepted <@ D.submit(operation, view, state);
    return (D.differential_win, D.query_count);
  }
}.

module HonestEditAcceptanceWitness = {
  module E = ProtocolEnvironment(TestSignature, TestNodeHash)

  proc main() : bool * int = {
    var fixture : witness_fixture;
    var envelope : operation_envelope;
    var operation : signed_operation;
    var accepted : bool;

    fixture <@ WitnessFixtures.base();
    envelope <- witness_edit_envelope
      (ProtocolDomain 1)
      (1)
      (witness_document)
      (OperationId 100)
      (witness_bob_old)
      (CapEdit)
      (fset1 witness_base_node)
      (authorization_digest_of fixture.`wf_authorization)
      (witness_edit_body_one)
      (Nonce 100);
    operation <@ WitnessFixtures.sign_operation(
      Production,
      envelope,
      witness_bob_old.`p_verification_key
    );

    E.init(Production, fixture.`wf_state, fixture.`wf_facts);
    accepted <@ E.submit(operation);
    return (accepted, size E.query_log);
  }
}.

module NonCanonicalRejectionWitness = {
  proc main() : bool = {
    var fixture : witness_fixture;
    var envelope : operation_envelope;
    var operation : signed_operation;
    var canonical_operation : signed_operation;
    var result : validation_result;
    var view : public_view;

    fixture <@ WitnessFixtures.base();
    envelope <- witness_edit_envelope
      (ProtocolDomain 1)
      (1)
      (witness_document)
      (OperationId 101)
      (witness_bob_old)
      (CapEdit)
      (fset1 witness_base_node)
      (authorization_digest_of fixture.`wf_authorization)
      (witness_edit_body_one)
      (Nonce 101);
    canonical_operation <@ WitnessFixtures.sign_operation(
      Production,
      envelope,
      witness_bob_old.`p_verification_key
    );
    operation <-
      {| so_raw = NonCanonicalWire envelope (RawBytes 1);
         so_signature = canonical_operation.`so_signature |};
    view <- witness_public_view (fixture.`wf_facts) (witness_context_7);
    result <@ ValidateOperation(TestSignature).validate(
      Production,
      operation,
      view,
      fixture.`wf_state
    );
    return ! result.`vr_accepted;
  }
}.

module MutationOperationSignature = {
  proc main() : bool * int = {
    var fixture : witness_fixture;
    var envelope : operation_envelope;
    var operation : signed_operation;

    var outcome : bool * int;
    fixture <@ WitnessFixtures.base();
    envelope <- witness_edit_envelope
      (ProtocolDomain 1)
      (1)
      (witness_document)
      (OperationId 201)
      (witness_bob_old)
      (CapEdit)
      (fset1 witness_base_node)
      (authorization_digest_of fixture.`wf_authorization)
      (witness_edit_body_one)
      (Nonce 201);
    operation <-
      {| so_raw = encode_operation envelope;
         so_signature =
           {| sig_verification_key = witness_bob_old.`p_verification_key;
              sig_bytes =
                SignatureBytes
                  (AuthorizationFactSignatureMessage witness_fact_1) |} |};
    outcome <@ StatefulMutationRunner.run(
      DefenseOperationSignature,
      fixture,
      operation
    );
    return outcome;
  }
}.

module MutationAuthorKeyBinding = {
  proc main() : bool * int = {
    var fixture : witness_fixture;
    var envelope : operation_envelope;
    var operation : signed_operation;

    var outcome : bool * int;
    fixture <@ WitnessFixtures.base();
    envelope <- witness_edit_envelope
      (ProtocolDomain 1)
      (1)
      (witness_document)
      (OperationId 202)
      (witness_bob_old)
      (CapEdit)
      (fset1 witness_base_node)
      (authorization_digest_of fixture.`wf_authorization)
      (witness_edit_body_one)
      (Nonce 202);
    operation <@ WitnessFixtures.sign_operation(
      Production,
      envelope,
      witness_alice.`p_verification_key
    );
    outcome <@ StatefulMutationRunner.run(
      DefenseAuthorKeyBinding,
      fixture,
      operation
    );
    return outcome;
  }
}.

module MutationIncarnationBinding = {
  proc main() : bool * int = {
    var fixture : witness_fixture;
    var envelope : operation_envelope;
    var operation : signed_operation;

    var outcome : bool * int;
    fixture <@ WitnessFixtures.rejoin();
    envelope <- witness_edit_envelope
      (ProtocolDomain 1)
      (1)
      (witness_document)
      (OperationId 203)
      (witness_bob_old)
      (CapEdit)
      (fset1 witness_rejoin_node)
      (authorization_digest_of fixture.`wf_authorization)
      (witness_edit_body_one)
      (Nonce 203);
    operation <@ WitnessFixtures.sign_operation(
      Production,
      envelope,
      witness_bob_old.`p_verification_key
    );
    outcome <@ StatefulMutationRunner.run(
      DefenseIncarnationBinding,
      fixture,
      operation
    );
    return outcome;
  }
}.

module MutationDocumentBinding = {
  proc main() : bool * int = {
    var fixture : witness_fixture;
    var envelope : operation_envelope;
    var operation : signed_operation;

    var outcome : bool * int;
    fixture <@ WitnessFixtures.base();
    envelope <- witness_edit_envelope
      (ProtocolDomain 1)
      (1)
      (witness_other_document)
      (OperationId 204)
      (witness_bob_old)
      (CapEdit)
      (fset1 witness_base_node)
      (authorization_digest_of fixture.`wf_authorization)
      (witness_edit_body_one)
      (Nonce 204);
    operation <@ WitnessFixtures.sign_operation(
      Production,
      envelope,
      witness_bob_old.`p_verification_key
    );
    outcome <@ StatefulMutationRunner.run(
      DefenseDocumentBinding,
      fixture,
      operation
    );
    return outcome;
  }
}.

module MutationDomainVersion = {
  proc main() : bool * int = {
    var fixture : witness_fixture;
    var envelope : operation_envelope;
    var operation : signed_operation;

    var outcome : bool * int;
    fixture <@ WitnessFixtures.base();
    envelope <- witness_edit_envelope
      (ProtocolDomain 2)
      (2)
      (witness_document)
      (OperationId 205)
      (witness_bob_old)
      (CapEdit)
      (fset1 witness_base_node)
      (authorization_digest_of fixture.`wf_authorization)
      (witness_edit_body_one)
      (Nonce 205);
    operation <@ WitnessFixtures.sign_operation(
      Production,
      envelope,
      witness_bob_old.`p_verification_key
    );
    outcome <@ StatefulMutationRunner.run(
      DefenseDomainVersion,
      fixture,
      operation
    );
    return outcome;
  }
}.

module MutationOperationBodyBinding = {
  proc main() : bool * int = {
    var fixture : witness_fixture;
    var signed_envelope : operation_envelope;
    var submitted_envelope : operation_envelope;
    var original : signed_operation;
    var operation : signed_operation;

    var outcome : bool * int;
    fixture <@ WitnessFixtures.base();
    signed_envelope <- witness_edit_envelope
      (ProtocolDomain 1)
      (1)
      (witness_document)
      (OperationId 206)
      (witness_bob_old)
      (CapEdit)
      (fset1 witness_base_node)
      (authorization_digest_of fixture.`wf_authorization)
      (witness_edit_body_one)
      (Nonce 206);
    submitted_envelope <- witness_edit_envelope
      (ProtocolDomain 1)
      (1)
      (witness_document)
      (OperationId 206)
      (witness_bob_old)
      (CapEdit)
      (fset1 witness_base_node)
      (authorization_digest_of fixture.`wf_authorization)
      (witness_edit_body_two)
      (Nonce 206);
    original <@ WitnessFixtures.sign_operation(
      WithoutDefense DefenseOperationBodyBinding,
      signed_envelope,
      witness_bob_old.`p_verification_key
    );
    operation <-
      {| so_raw = encode_operation submitted_envelope;
         so_signature = original.`so_signature |};
    outcome <@ StatefulMutationRunner.run(
      DefenseOperationBodyBinding,
      fixture,
      operation
    );
    return outcome;
  }
}.

module MutationRequiredCapabilityBinding = {
  proc main() : bool * int = {
    var fixture : witness_fixture;
    var signed_envelope : operation_envelope;
    var submitted_envelope : operation_envelope;
    var original : signed_operation;
    var operation : signed_operation;

    var outcome : bool * int;
    fixture <@ WitnessFixtures.base();
    signed_envelope <- witness_edit_envelope
      (ProtocolDomain 1)
      (1)
      (witness_document)
      (OperationId 207)
      (witness_alice)
      (CapEdit)
      (fset1 witness_base_node)
      (authorization_digest_of fixture.`wf_authorization)
      (witness_delete_body)
      (Nonce 207);
    submitted_envelope <- witness_edit_envelope
      (ProtocolDomain 1)
      (1)
      (witness_document)
      (OperationId 207)
      (witness_alice)
      (CapAdmin)
      (fset1 witness_base_node)
      (authorization_digest_of fixture.`wf_authorization)
      (witness_delete_body)
      (Nonce 207);
    original <@ WitnessFixtures.sign_operation(
      WithoutDefense DefenseRequiredCapabilityBinding,
      signed_envelope,
      witness_alice.`p_verification_key
    );
    operation <-
      {| so_raw = encode_operation submitted_envelope;
         so_signature = original.`so_signature |};
    outcome <@ StatefulMutationRunner.run(
      DefenseRequiredCapabilityBinding,
      fixture,
      operation
    );
    return outcome;
  }
}.

module MutationExactCausalContext = {
  proc main() : bool * int = {
    var fixture : witness_fixture;
    var envelope : operation_envelope;
    var operation : signed_operation;
    var view : public_view;

    var outcome : bool * int;
    fixture <@ WitnessFixtures.base();
    envelope <- witness_edit_envelope
      (ProtocolDomain 1)
      (1)
      (witness_document)
      (OperationId 208)
      (witness_bob_old)
      (CapEdit)
      (fset1 witness_base_node)
      (authorization_digest_of fixture.`wf_authorization)
      (witness_edit_body_one)
      (Nonce 208);
    operation <@ WitnessFixtures.sign_operation(
      Production,
      envelope,
      witness_bob_old.`p_verification_key
    );
    view <- witness_public_view (fixture.`wf_facts) (witness_context_6);
    outcome <@ DirectMutationRunner.run(
      DefenseExactCausalContext,
      operation,
      view,
      fixture.`wf_state
    );
    return outcome;
  }
}.

module MutationAuthorizationDigest = {
  proc main() : bool * int = {
    var fixture : witness_fixture;
    var envelope : operation_envelope;
    var operation : signed_operation;

    var outcome : bool * int;
    fixture <@ WitnessFixtures.extended();
    envelope <- witness_edit_envelope
      (ProtocolDomain 1)
      (1)
      (witness_document)
      (OperationId 209)
      (witness_bob_old)
      (CapEdit)
      (fset1 witness_extended_node)
      (InvalidAuthorizationDigest 7)
      (witness_edit_body_one)
      (Nonce 209);
    operation <@ WitnessFixtures.sign_operation(
      Production,
      envelope,
      witness_bob_old.`p_verification_key
    );
    outcome <@ StatefulMutationRunner.run(
      DefenseAuthorizationDigest,
      fixture,
      operation
    );
    return outcome;
  }
}.

module MutationPredecessorCompleteness = {
  proc main() : bool * int = {
    var fixture : witness_fixture;
    var envelope : operation_envelope;
    var operation : signed_operation;
    var view : public_view;

    var outcome : bool * int;
    fixture <@ WitnessFixtures.missing_revocation();
    envelope <- witness_edit_envelope
      (ProtocolDomain 1)
      (1)
      (witness_document)
      (OperationId 210)
      (witness_bob_old)
      (CapEdit)
      (fset1 witness_missing_revoke_node)
      (authorization_digest_of fixture.`wf_authorization)
      (witness_edit_body_one)
      (Nonce 210);
    operation <@ WitnessFixtures.sign_operation(
      Production,
      envelope,
      witness_bob_old.`p_verification_key
    );
    view <- witness_public_view (fixture.`wf_facts) (witness_context_7);
    outcome <@ DirectMutationRunner.run(
      DefensePredecessorCompleteness,
      operation,
      view,
      fixture.`wf_state
    );
    return outcome;
  }
}.

module MutationGrantRecipientBinding = {
  proc main() : bool * int = {
    var fixture : witness_fixture;
    var envelope : operation_envelope;
    var operation : signed_operation;

    var outcome : bool * int;
    fixture <@ WitnessFixtures.base();
    envelope <- witness_history_envelope
      (OperationId 211)
      (authorization_digest_of fixture.`wf_authorization)
      (witness_carol)
      (witness_merge_node)
      (witness_region)
      (witness_cover)
      (Nonce 211);
    operation <@ WitnessFixtures.sign_operation(
      Production,
      envelope,
      witness_alice.`p_verification_key
    );
    outcome <@ StatefulMutationRunner.run(
      DefenseGrantRecipientBinding,
      fixture,
      operation
    );
    return outcome;
  }
}.

module MutationMergeNodeBinding = {
  proc main() : bool * int = {
    var fixture : witness_fixture;
    var envelope : operation_envelope;
    var operation : signed_operation;

    var outcome : bool * int;
    fixture <@ WitnessFixtures.base();
    envelope <- witness_history_envelope
      (OperationId 212)
      (authorization_digest_of fixture.`wf_authorization)
      (witness_bob_old)
      (witness_other_merge_node)
      (witness_region)
      (witness_cover)
      (Nonce 212);
    operation <@ WitnessFixtures.sign_operation(
      Production,
      envelope,
      witness_alice.`p_verification_key
    );
    outcome <@ StatefulMutationRunner.run(
      DefenseMergeNodeBinding,
      fixture,
      operation
    );
    return outcome;
  }
}.

module MutationRegionBinding = {
  proc main() : bool * int = {
    var fixture : witness_fixture;
    var envelope : operation_envelope;
    var operation : signed_operation;

    var outcome : bool * int;
    fixture <@ WitnessFixtures.base();
    envelope <- witness_history_envelope
      (OperationId 213)
      (authorization_digest_of fixture.`wf_authorization)
      (witness_bob_old)
      (witness_merge_node)
      (witness_enlarged_region)
      (witness_cover)
      (Nonce 213);
    operation <@ WitnessFixtures.sign_operation(
      Production,
      envelope,
      witness_alice.`p_verification_key
    );
    outcome <@ StatefulMutationRunner.run(
      DefenseRegionBinding,
      fixture,
      operation
    );
    return outcome;
  }
}.

module MutationSegmentBinding = {
  proc main() : bool * int = {
    var fixture : witness_fixture;
    var envelope : operation_envelope;
    var operation : signed_operation;

    var outcome : bool * int;
    fixture <@ WitnessFixtures.base();
    envelope <- witness_history_envelope
      (OperationId 214)
      (authorization_digest_of fixture.`wf_authorization)
      (witness_bob_old)
      (witness_merge_node)
      (witness_region)
      (witness_cross_segment_cover)
      (Nonce 214);
    operation <@ WitnessFixtures.sign_operation(
      Production,
      envelope,
      witness_alice.`p_verification_key
    );
    outcome <@ StatefulMutationRunner.run(
      DefenseSegmentBinding,
      fixture,
      operation
    );
    return outcome;
  }
}.
