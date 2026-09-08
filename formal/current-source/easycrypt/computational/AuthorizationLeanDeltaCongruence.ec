require import AllCore List FSet.
require import ProtocolTypes CanonicalEncoding AuthorizationState AuthorizationRepresentation.
require import AuthorizationLeanDeltaMapping.

(* Extensional equality is stated as a predicate because the Lean projection
   stores its observed-remove relations as functions.  These congruence lemmas
   let the full replay proof replace each successful validator transition by
   the independently defined Lean delta from AuthorizationLeanDeltaMapping. *)
lemma authorization_representation_iff_projection_equiv
    (state : authorization_state)
    (model : lean_observed_remove_authorization) :
  authorization_state_represents_lean state model <=>
  lean_authorization_equiv (project_authorization_state state) model.
proof.
  rewrite /authorization_state_represents_lean /lean_authorization_equiv
    /project_authorization_state /=.
  smt().
qed.

lemma lean_authorization_equiv_reflexive
    (model : lean_observed_remove_authorization) :
  lean_authorization_equiv model model.
proof. by rewrite /lean_authorization_equiv. qed.

lemma lean_authorization_equiv_transitive
    (lhs middle rhs : lean_observed_remove_authorization) :
  lean_authorization_equiv lhs middle =>
  lean_authorization_equiv middle rhs =>
  lean_authorization_equiv lhs rhs.
proof.
  rewrite /lean_authorization_equiv.
  smt().
qed.

lemma lean_authorization_join_respects_equiv
    (lhs rhs addition : lean_observed_remove_authorization) :
  lean_authorization_equiv lhs rhs =>
  lean_authorization_equiv
    (lean_authorization_join lhs addition)
    (lean_authorization_join rhs addition).
proof.
  rewrite /lean_authorization_equiv /lean_authorization_join.
  smt().
qed.

lemma lean_apply_signed_authorization_facts_from_respects_equiv
    (facts : signed_authorization_fact list) :
  forall lhs rhs,
    lean_authorization_equiv lhs rhs =>
    lean_authorization_equiv
      (lean_apply_signed_authorization_facts_from lhs facts)
      (lean_apply_signed_authorization_facts_from rhs facts).
proof.
  elim: facts => [| signed_fact rest ih] lhs rhs equivalent.
  + by rewrite /lean_apply_signed_authorization_facts_from /=.
  + rewrite /lean_apply_signed_authorization_facts_from /=.
    apply ih.
    exact (lean_authorization_join_respects_equiv
      lhs rhs
      (lean_authorization_delta_of_fact signed_fact.`saf_fact)
      equivalent).
qed.
