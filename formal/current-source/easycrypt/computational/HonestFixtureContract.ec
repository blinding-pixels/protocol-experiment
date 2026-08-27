require import AllCore List FSet.
require import ProtocolTypes CanonicalEncoding ProtocolPrimitives AuthorizationState.
require import ProtocolChecks ProtocolOracles UnauthorizedGame WitnessFixtures.
require import AuthorizationWitnessTrace AuthorizationNormalizerContract.

(* Exact concrete fixture returned by [WitnessFixtures.base].  This packages
   the checker-proved seven-fact normalizer result for reuse by the production
   acceptance proof without re-expanding the normalizer loop. *)
op witness_base_fixture_exact : witness_fixture =
  {| wf_state =
       witness_protocol_state witness_base_node witness_context_7;
     wf_facts = witness_base_signed_facts;
     wf_authorization_valid = true;
     wf_authorization = witness_authorization_state_7 |}.

lemma witness_base_fixture_contract :
  hoare [WitnessFixtures.base :
    true ==> res = witness_base_fixture_exact].
proof.
  proc.
  inline WitnessFixtures.sign_fact TestSignature.sign.
  ecall (normalize_witness_base_signed_facts).
  auto;
  rewrite /witness_base_fixture_exact
    /witness_base_signed_facts
    /witness_signed_fact_1 /witness_signed_fact_2
    /witness_signed_fact_3 /witness_signed_fact_4
    /witness_signed_fact_5 /witness_signed_fact_6
    /witness_signed_fact_7 /witness_signed_fact_of.
qed.
