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
    current snapshots creator final_state replay.
  + rewrite /authorization_policy_replay_from in replay.
    have final_eq : final_state = current by smt().
    rewrite final_eq /lean_apply_signed_authorization_facts_from.
    exact (project_authorization_state_represents current).
  + rewrite /authorization_policy_replay_from in replay.
    case: (authorization_snapshot_lookup
      signed_fact.`saf_fact.`af_context snapshots = None) => context_missing.
    + by rewrite context_missing in replay.
    have context_some := authorization_state_option_some_oget
      (authorization_snapshot_lookup
        signed_fact.`saf_fact.`af_context snapshots)
      context_missing.
    rewrite context_some /= in replay.
    case: (apply_authorization_fact
      current
      (oget (authorization_snapshot_lookup
        signed_fact.`saf_fact.`af_context snapshots))
      creator
      signed_fact.`saf_fact = None) => next_missing.
    + by rewrite next_missing in replay.
    have next_some := authorization_state_option_some_oget
      (apply_authorization_fact
        current
        (oget (authorization_snapshot_lookup
          signed_fact.`saf_fact.`af_context snapshots))
        creator
        signed_fact.`saf_fact)
      next_missing.
    rewrite next_some /= in replay.
    have tail_representation :=
      ih
        (oget (apply_authorization_fact
          current
          (oget (authorization_snapshot_lookup
            signed_fact.`saf_fact.`af_context snapshots))
          creator
          signed_fact.`saf_fact))
        (rcons snapshots
          {| snapshot_context =
               (oget (apply_authorization_fact
                 current
                 (oget (authorization_snapshot_lookup
                   signed_fact.`saf_fact.`af_context snapshots))
                 creator
                 signed_fact.`saf_fact)).`as_fact_ids;
             snapshot_state =
               oget (apply_authorization_fact
                 current
                 (oget (authorization_snapshot_lookup
                   signed_fact.`saf_fact.`af_context snapshots))
                 creator
                 signed_fact.`saf_fact) |})
        creator final_state replay.
    have step_representation :=
      successful_fact_application_represents_lean_delta
        current
        (oget (authorization_snapshot_lookup
          signed_fact.`saf_fact.`af_context snapshots))
        (oget (apply_authorization_fact
          current
          (oget (authorization_snapshot_lookup
            signed_fact.`saf_fact.`af_context snapshots))
          creator
          signed_fact.`saf_fact))
        creator signed_fact.`saf_fact next_some.
    rewrite authorization_representation_iff_projection_equiv
      in step_representation.
    rewrite authorization_representation_iff_projection_equiv
      in tail_representation.
    have tail_models_equiv :=
      lean_apply_signed_authorization_facts_from_respects_equiv
        rest
        (project_authorization_state
          (oget (apply_authorization_fact
            current
            (oget (authorization_snapshot_lookup
              signed_fact.`saf_fact.`af_context snapshots))
            creator
            signed_fact.`saf_fact)))
        (lean_authorization_join
          (project_authorization_state current)
          (lean_authorization_delta_of_fact signed_fact.`saf_fact))
        step_representation.
    rewrite /lean_apply_signed_authorization_facts_from.
    rewrite authorization_representation_iff_projection_equiv.
    exact (lean_authorization_equiv_transitive
      (project_authorization_state final_state)
      (lean_apply_signed_authorization_facts_from
        (project_authorization_state
          (oget (apply_authorization_fact
            current
            (oget (authorization_snapshot_lookup
              signed_fact.`saf_fact.`af_context snapshots))
            creator
            signed_fact.`saf_fact)))
        rest)
      (lean_apply_signed_authorization_facts_from
        (lean_authorization_join
          (project_authorization_state current)
          (lean_authorization_delta_of_fact signed_fact.`saf_fact))
        rest)
      tail_representation tail_models_equiv).
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
