require import AllCore List FSet.
require import ProtocolTypes CanonicalEncoding ProtocolPrimitives AuthorizationState.

(* Pure policy replay.  This does not reimplement any authorization rule: each
   transition delegates to the same context lookup and
   [apply_authorization_fact] operator used by the production normalizer. *)
op authorization_policy_replay_from
    (current : authorization_state)
    (snapshots : authorization_snapshot list)
    (creator : principal)
    (facts : signed_authorization_fact list) : authorization_state option =
  with facts = [] => Some current
  with facts = signed_fact :: rest =>
    let fact = signed_fact.`saf_fact in
    let context_state =
      authorization_snapshot_lookup fact.`af_context snapshots in
    if context_state = None
    then None
    else
      let next_state =
        apply_authorization_fact current (oget context_state) creator fact in
      if next_state = None
      then None
      else
        let next = oget next_state in
        authorization_policy_replay_from
          next
          (rcons snapshots
            {| snapshot_context = next.`as_fact_ids;
               snapshot_state = next |})
          creator
          rest.

op authorization_policy_replay
    (creator : principal)
    (facts : signed_authorization_fact list) : authorization_state option =
  authorization_policy_replay_from
    empty_authorization_state
    [{| snapshot_context = fset0;
        snapshot_state = empty_authorization_state |}]
    creator
    facts.

pred authorization_ancestry_valid
    (creator : principal)
    (facts : signed_authorization_fact list)
    (state : authorization_state) =
  authorization_policy_replay creator facts = Some state.

section A3PolicyAncestry.
  declare module S <: SIGNATURE_SCHEME.

  lemma normalize_success_implies_policy_ancestry
      (input_facts : signed_authorization_fact list)
      (input_creator : principal) :
    hoare [NormalizeAuthorization(S).normalize :
      facts = input_facts /\ creator = input_creator ==>
      res.`1 =>
        authorization_ancestry_valid input_creator input_facts res.`2].
  proof.
    proc.
    while
      (valid =>
        authorization_policy_replay_from
          current snapshots creator remaining =
        authorization_policy_replay input_creator input_facts).
    + wp.
      call (_ : true ==> true).
      auto=> /> &hr.
      rewrite /authorization_policy_replay_from.
      smt().
    + auto; rewrite /authorization_policy_replay.
    + auto=> />.
      rewrite /authorization_ancestry_valid /authorization_policy_replay_from.
      smt().
  qed.
end section A3PolicyAncestry.

(* Direct consequences of a successful non-genesis ancestry step.  The issuer
   is authorized in the fact's own causal snapshot under exact production
   principal matching. *)
lemma non_genesis_issuer_has_exact_admin_authority
    (current context_state : authorization_state)
    (creator : principal)
    (fact : authorization_fact) :
  ! genesis_authorization_fact fact =>
  authorization_issuer_allowed current context_state creator fact =>
     member_active Production context_state fact.`af_issuer
  /\ capability_active Production context_state fact.`af_issuer CapAdmin.
proof.
  by move=> non_genesis; rewrite /authorization_issuer_allowed non_genesis.
qed.

lemma successful_membership_revoke_observes_known_tags
    (current context_state : authorization_state)
    (creator : principal)
    (fact : authorization_fact)
    (next : authorization_state) :
  fact.`af_kind = MembershipRevoke =>
  apply_authorization_fact current context_state creator fact = Some next =>
  all_member_tags_known current (elems fact.`af_observed_member_tags).
proof.
  move=> kind applied.
  rewrite /apply_authorization_fact in applied.
  case: (! authorization_fact_shape_valid fact \/
         fact.`af_id \in current.`as_fact_ids \/
         ! authorization_issuer_allowed current context_state creator fact)
    applied=> //= applied.
  rewrite /apply_authorization_fact_kind kind in applied.
  by case: (! all_member_tags_known current
       (elems fact.`af_observed_member_tags)) applied=> //= /#.
qed.

lemma successful_capability_revoke_observes_known_tags
    (current context_state : authorization_state)
    (creator : principal)
    (fact : authorization_fact)
    (next : authorization_state) :
  fact.`af_kind = CapabilityRevoke =>
  apply_authorization_fact current context_state creator fact = Some next =>
  all_capability_tags_known current
    (elems fact.`af_observed_capability_tags).
proof.
  move=> kind applied.
  rewrite /apply_authorization_fact in applied.
  case: (! authorization_fact_shape_valid fact \/
         fact.`af_id \in current.`as_fact_ids \/
         ! authorization_issuer_allowed current context_state creator fact)
    applied=> //= applied.
  rewrite /apply_authorization_fact_kind kind in applied.
  by case: (! all_capability_tags_known current
       (elems fact.`af_observed_capability_tags)) applied=> //= /#.
qed.

lemma successful_membership_grant_does_not_revive_retired_principal
    (current context_state : authorization_state)
    (creator : principal)
    (fact : authorization_fact)
    (next : authorization_state) :
  fact.`af_kind = MembershipGrant =>
  apply_authorization_fact current context_state creator fact = Some next =>
  oget fact.`af_target \notin current.`as_retired_principals.
proof.
  move=> kind applied.
  rewrite /apply_authorization_fact in applied.
  case: (! authorization_fact_shape_valid fact \/
         fact.`af_id \in current.`as_fact_ids \/
         ! authorization_issuer_allowed current context_state creator fact)
    applied=> //= applied.
  rewrite /apply_authorization_fact_kind kind in applied.
  by case: (member_tag_known current (oget fact.`af_member_tag) \/
       oget fact.`af_target \in current.`as_retired_principals)
    applied=> //= /#.
qed.
