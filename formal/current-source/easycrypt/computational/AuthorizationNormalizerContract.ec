require import AllCore List FSet.
require import ProtocolTypes CanonicalEncoding ProtocolPrimitives AuthorizationState WitnessFixtures.
require import AuthorizationWitnessTrace AuthorizationNormalizerExecutionComplete.

(* Canonical name for the complete honest normalizer contract. *)

lemma witness_signed_facts_7_eq_base :
  witness_signed_facts_7 = witness_base_signed_facts.
proof.
  by rewrite /witness_signed_facts_7 /witness_base_signed_facts.
qed.

lemma normalize_witness_base_signed_facts :
  hoare [NormalizeAuthorization(TestSignature).normalize :
    facts = witness_base_signed_facts /\ creator = witness_alice ==>
    res = (true, witness_authorization_state_7)].
proof.
  conseq normalize_witness_prefix_7 => //.
qed.
