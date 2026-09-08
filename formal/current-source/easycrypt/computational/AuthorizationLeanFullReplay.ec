require import AllCore List FSet.
require import ProtocolTypes CanonicalEncoding AuthorizationState AuthorizationAncestry AuthorizationRepresentation.
require import AuthorizationLeanDeltaMapping AuthorizationLeanDeltaCongruence.

lemma authorization_state_option_some_oget
    (candidate : authorization_state option) :
  candidate <> None => candidate = Some (oget candidate).
proof. by case: candidate. qed.

lemma authorization_policy_replay_from_matches_independent_lean_apply
    (facts : signed_authorization_fact list) :
  forall current snapshots creator final_state,
    authorization_policy_replay_from current snapshots creator facts =
      Some final_state =>
    authorization_state_represents_lean
      final_state
      (lean_apply_signed_authorization_facts_from
        (project_authorization_state current) facts).
proof.
  elim: facts => [| signed_fact rest ih]
    current snapshots creator final_state.
  + rewrite /authorization_policy_replay_from /=.
    move=> replay.
    have final_eq : final_state = current by smt().
    rewrite final_eq /lean_apply_signed_authorization_facts_from /=.
    exact (project_authorization_state_represents current).
  + rewrite /authorization_policy_replay_from /=.
    case _: (authorization_snapshot_lookup
      signed_fact.`saf_fact.`af_context snapshots) => [|context_state] Hcontext //=.
    case _: (apply_authorization_fact
      current context_state creator signed_fact.`saf_fact) => [|next_state] Hnext //=.
    move=> Htail.
    have step_representation :=
      successful_fact_application_represents_lean_delta
        current context_state next_state creator signed_fact.`saf_fact Hnext.
    have tail_representation := ih next_state
      (rcons snapshots {| snapshot_context = next_state.`as_fact_ids;
                          snapshot_state = next_state |})
      creator final_state Htail.
    move: step_representation tail_representation.
    rewrite !authorization_representation_iff_projection_equiv.
    move=> Hstep Hresult.
    have Hmodels := lean_apply_signed_authorization_facts_from_respects_equiv
      rest (project_authorization_state next_state)
      (lean_authorization_join (project_authorization_state current)
        (lean_authorization_delta_of_fact signed_fact.`saf_fact)) Hstep.
    exact (lean_authorization_equiv_transitive
      (project_authorization_state final_state)
      (lean_apply_signed_authorization_facts_from
        (project_authorization_state next_state) rest)
      (lean_apply_signed_authorization_facts_from
        (lean_authorization_join (project_authorization_state current)
          (lean_authorization_delta_of_fact signed_fact.`saf_fact)) rest)
      Hresult Hmodels).
qed.

lemma authorization_policy_replay_matches_independent_lean_apply
    (creator : principal)
    (facts : signed_authorization_fact list)
    (state : authorization_state) :
  authorization_policy_replay creator facts = Some state =>
  authorization_state_represents_lean
    state (lean_apply_signed_authorization_facts facts).
proof.
  move=> replay.
  rewrite /authorization_policy_replay in replay.
  have replay_representation :=
    authorization_policy_replay_from_matches_independent_lean_apply
      facts
      empty_authorization_state
      [{| snapshot_context = fset0;
          snapshot_state = empty_authorization_state |}]
      creator state replay.
  rewrite authorization_representation_iff_projection_equiv
    in replay_representation.
  have empty_representation := lean_empty_represents_empty_authorization.
  rewrite authorization_representation_iff_projection_equiv
    in empty_representation.
  have replay_models_equiv :=
    lean_apply_signed_authorization_facts_from_respects_equiv
      facts
      (project_authorization_state empty_authorization_state)
      lean_authorization_empty
      empty_representation.
  rewrite /lean_apply_signed_authorization_facts.
  rewrite authorization_representation_iff_projection_equiv.
  exact (lean_authorization_equiv_transitive
    (project_authorization_state state)
    (lean_apply_signed_authorization_facts_from
      (project_authorization_state empty_authorization_state) facts)
    (lean_apply_signed_authorization_facts_from
      lean_authorization_empty facts)
    replay_representation replay_models_equiv).
qed.

lemma authorization_ancestry_matches_independent_lean_apply
    (creator : principal)
    (facts : signed_authorization_fact list)
    (state : authorization_state) :
  authorization_ancestry_valid creator facts state =>
  authorization_state_represents_lean
    state (lean_apply_signed_authorization_facts facts).
proof.
  rewrite /authorization_ancestry_valid.
  exact (authorization_policy_replay_matches_independent_lean_apply
    creator facts state).
qed.
