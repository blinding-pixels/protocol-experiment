require import UnauthorizedReductionNext UnauthorizedOriginFinalBound.
require import PrimitiveControlProofs MutationHistoryProofs MutationPolicyProofs.
require import MutationEditProofs MutationGameProofs MutationProofs.
require import HonestOperationContract UnauthorizedOriginPartition.
require import AuthorizationLeanFullReplay CausalClosureRepresentation.
require import LiveKeyGame LiveKeyWitnesses LiveAuthenticationReduction.
require import LiveBeeKemControl LiveBeeKemDerived.
require import LiveBeeKemOracle LiveBeeKemReduction.
require import LivePrfReduction.

(* Authoritative Deliverable A entry point.

   Importing [UnauthorizedReductionNext] forces the complete active A0--A5,
   direct operation/fact forgery, hash-collision, independent Lean-fold,
   validator, mutation, and anti-vacuity dependency closure through the
   EasyCrypt kernel.  The declarations below expose the public theorem and its
   load-bearing controls rather than leaving the completed reduction hidden
   behind the development-only milestone entry point. *)

print UnauthorizedOriginFinalBound.adv_unauthorized_origin_bound.
print UnauthorizedOriginPartition.origin_ideal_probability_zero.
print UnauthorizedOriginFinalBound.encoding_failure_probability_zero.
print UnauthorizedOriginFinalBound.distinct_envelopes_have_distinct_canonical_encodings.
print AuthorizationLeanFullReplay.authorization_policy_replay_matches_independent_lean_apply.
print CausalClosureRepresentation.represented_exact_predecessor_closure.

(* Non-vacuity and primitive connectivity controls. *)
print HonestOperationContract.witness_honest_operation_accepted.
print MutationProofs.noncanonical_rejection_probability_one.
print PrimitiveControlProofs.test_signature_multi_user_eufcma_probability_one.

(* Deliverable A one-defense-removed differential matrix.  Each probability-one
   theorem depends on a production-rejection lemma and a matching
   single-defense-removed acceptance lemma in the same proof module. *)
print MutationGameProofs.mutation_operation_signature_wins_probability_one.
print MutationEditProofs.mutation_author_key_wins_probability_one.
print MutationEditProofs.mutation_incarnation_wins_probability_one.
print MutationEditProofs.mutation_document_wins_probability_one.
print MutationEditProofs.mutation_domain_wins_probability_one.
print MutationPolicyProofs.mutation_body_wins_probability_one.
print MutationPolicyProofs.mutation_capability_wins_probability_one.
print MutationPolicyProofs.mutation_context_wins_probability_one.
print MutationPolicyProofs.mutation_digest_wins_probability_one.
print MutationPolicyProofs.mutation_predecessor_wins_probability_one.
print MutationHistoryProofs.mutation_recipient_wins_probability_one.
print MutationHistoryProofs.mutation_merge_wins_probability_one.
print MutationHistoryProofs.mutation_region_wins_probability_one.
print MutationHistoryProofs.mutation_segment_wins_probability_one.

(* Deliverable L checkpoint 1: executable game and non-vacuity controls. *)
print LiveKeyWitnesses.honest_live_trace_reaches_admissible_challenge.
print LiveKeyWitnesses.previously_revealed_live_node_cannot_be_challenged.
print LiveKeyWitnesses.single_challenge_without_compromise_is_bee_safe.
print LiveKeyWitnesses.immediate_same_node_compromise_is_not_bee_safe.

(* Deliverable L checkpoint 2: the exact live execution is installed inside
   Deliverable A's origin-tracked validator environment. *)
print LiveAuthenticationReduction.live_success_le_authenticated_plus_origin_failure.
print LiveAuthenticationReduction.live_authentication_failure_exactly_deliverable_a.
print LiveAuthenticationReduction.live_authentication_failure_bound.

(* Deliverable L checkpoint 3: concrete KI-DCGKA runtime adapter. *)
print LiveBeeKemReduction.beekem_live_wrapper_invokes_primitive_challenge_once.

(* Deliverable L checkpoint 4-in-progress: application multi-domain PRF game. *)
print LivePrfReduction.mdprf_live_domain_is_not_history_domain.
print LivePrfReduction.mdprf_live_domain_is_not_history_capability_domain.
print LivePrfReduction.bprf_live_fixed_real_control.
print LivePrfReduction.bprf_live_fixed_random_control.
print LivePrfReduction.insecure_test_kdf_prf_game_probability_one.
print LivePrfReduction.insecure_test_kdf_prf_normalized_advantage_half.
