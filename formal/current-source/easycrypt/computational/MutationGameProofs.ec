require import AllCore List FSet.
require import ProtocolTypes CanonicalEncoding ProtocolPrimitives AuthorizationState.
require import ProtocolChecks ProtocolOracles UnauthorizedGame WitnessFixtures MutationWitnesses.
require import AuthorizationWitnessTrace AuthorizationNormalizerWitness.
require import HonestOperationContract ValidatorCharacterization.

(* A single-query differential harness that invokes the actual public validator
   twice: once in Production and once with exactly the selected defense removed.
   The returned query count is part of every mutation theorem, ruling out an
   unreachable or decorative witness. *)
module CheckedMutationRunner = {
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

lemma checked_mutation_runner_lossless :
  islossless CheckedMutationRunner.run.
proof.
  proc.
  call witness_honest_validate_lossless.
  call witness_honest_validate_lossless.
  auto.
qed.

lemma base_facts_edit_differential_submit_wins
    (removed : defense)
    (input_operation : signed_operation)
    (input_envelope : operation_envelope)
    (input_view : public_view)
    (input_state : protocol_state) :
     input_view.`pv_facts = witness_base_signed_facts
  => input_state.`ps_creator = witness_alice
  => decode_operation input_operation.`so_raw = Some input_envelope
  => input_envelope.`oe_operation_kind = OpEdit
  => canonical_reencoding input_operation.`so_raw
  => ! base_facts_edit_decoded_accepts Production input_operation
       input_envelope input_view input_state
  => base_facts_edit_decoded_accepts
       (WithoutDefense removed) input_operation input_envelope
       input_view input_state
  => hoare [CheckedMutationRunner.D.submit :
         CheckedMutationRunner.D.removed_defense = removed
      /\ ! CheckedMutationRunner.D.differential_win
      /\ CheckedMutationRunner.D.query_count = 0
      /\ operation = input_operation
      /\ view = input_view
      /\ state = input_state
      ==>
         res
      /\ CheckedMutationRunner.D.differential_win
      /\ CheckedMutationRunner.D.query_count = 1].
proof.
  move=> Hfacts Hcreator Hdecode Hkind Hcanonical Hproduction Hmutated.
  proc.
  call (base_facts_edit_validate_characterization
    (WithoutDefense removed) input_operation input_envelope
    input_view input_state).
  call (base_facts_edit_validate_characterization
    Production input_operation input_envelope input_view input_state).
  auto=> />.
  smt().
qed.

lemma base_facts_edit_mutation_run_wins
    (removed : defense)
    (input_operation : signed_operation)
    (input_envelope : operation_envelope)
    (input_view : public_view)
    (input_state : protocol_state) :
     input_view.`pv_facts = witness_base_signed_facts
  => input_state.`ps_creator = witness_alice
  => decode_operation input_operation.`so_raw = Some input_envelope
  => input_envelope.`oe_operation_kind = OpEdit
  => canonical_reencoding input_operation.`so_raw
  => ! base_facts_edit_decoded_accepts Production input_operation
       input_envelope input_view input_state
  => base_facts_edit_decoded_accepts
       (WithoutDefense removed) input_operation input_envelope
       input_view input_state
  => hoare [CheckedMutationRunner.run :
         removed = removed{hr}
      /\ operation = input_operation
      /\ view = input_view
      /\ state = input_state
      ==>
      res = (true, 1)].
proof.
  move=> Hfacts Hcreator Hdecode Hkind Hcanonical Hproduction Hmutated.
  proc.
  inline CheckedMutationRunner.D.init.
  call (base_facts_edit_differential_submit_wins
    removed{hr} input_operation input_envelope input_view input_state
    Hfacts Hcreator Hdecode Hkind Hcanonical Hproduction Hmutated).
  auto.
qed.

op mutation_operation_signature_operation : signed_operation =
  {| so_raw = encode_operation witness_honest_edit_envelope;
     so_signature =
       {| sig_verification_key = witness_bob_old.`p_verification_key;
          sig_bytes =
            SignatureBytes
              (AuthorizationFactSignatureMessage witness_fact_1) |} |}.

lemma mutation_operation_signature_decodes :
  decode_operation mutation_operation_signature_operation.`so_raw =
    Some witness_honest_edit_envelope.
proof.
  by rewrite /mutation_operation_signature_operation.
qed.

lemma mutation_operation_signature_canonical :
  canonical_reencoding mutation_operation_signature_operation.`so_raw.
proof.
  by rewrite /mutation_operation_signature_operation.
qed.

lemma mutation_operation_signature_production_rejects :
  ! base_facts_edit_decoded_accepts
      Production
      mutation_operation_signature_operation
      witness_honest_edit_envelope
      witness_base_view_exact
      witness_base_state_exact.
proof.
  rewrite /base_facts_edit_decoded_accepts /base_facts_common_accepts
    /mutation_operation_signature_operation
    /operation_signature_message /defense_enabled.
  smt().
qed.

lemma mutation_operation_signature_removed_accepts :
  base_facts_edit_decoded_accepts
    (WithoutDefense DefenseOperationSignature)
    mutation_operation_signature_operation
    witness_honest_edit_envelope
    witness_base_view_exact
    witness_base_state_exact.
proof.
  rewrite /base_facts_edit_decoded_accepts /base_facts_common_accepts
    /mutation_operation_signature_operation /defense_enabled.
  rewrite witness_honest_predecessors_exist witness_honest_exact_closure
    witness_base_view_facts witness_base_fact_ids
    witness_base_view_observed_fact_ids
    witness_honest_authorization_digest
    witness_honest_author_key_binding
    witness_honest_author witness_honest_required_capability_field
    witness_bob_old_member_active_state_7
    witness_bob_old_edit_active_state_7
    witness_honest_required_capability
    witness_honest_operation_body_valid.
  smt(witness_honest_domain_version witness_honest_document_binding
    witness_honest_freshness).
qed.

lemma mutation_operation_signature_wins_probability_one &m :
  Pr[
    CheckedMutationRunner.run(
      DefenseOperationSignature,
      mutation_operation_signature_operation,
      witness_base_view_exact,
      witness_base_state_exact
    ) @ &m :
    res = (true, 1)
  ] = 1%r.
proof.
  byphoare
    (: removed = DefenseOperationSignature
       /\ operation = mutation_operation_signature_operation
       /\ view = witness_base_view_exact
       /\ state = witness_base_state_exact
       ==>
       res = (true, 1)) => //.
  + conseq (base_facts_edit_mutation_run_wins
      DefenseOperationSignature
      mutation_operation_signature_operation
      witness_honest_edit_envelope
      witness_base_view_exact
      witness_base_state_exact) => //.
    + exact witness_base_view_facts.
    + exact witness_base_state_creator.
    + exact mutation_operation_signature_decodes.
    + exact witness_honest_operation_kind.
    + exact mutation_operation_signature_canonical.
    + exact mutation_operation_signature_production_rejects.
    + exact mutation_operation_signature_removed_accepts.
  + conseq checked_mutation_runner_lossless => //.
qed.
