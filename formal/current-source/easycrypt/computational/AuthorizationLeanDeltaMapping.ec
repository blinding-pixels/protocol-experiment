require import AllCore List FSet.
require import ProtocolTypes CanonicalEncoding AuthorizationState AuthorizationRepresentation.

(* Independent transcription of the checked Lean observed-remove delta layer.
   Unlike [authorization_policy_replay], the definitions below do not call the
   EasyCrypt validator transition.  They only join the immutable delta denoted
   by each already-validated public fact, matching Lean's [applyAll] semantics. *)
op lean_authorization_empty : lean_observed_remove_authorization =
  {| lora_member_added = fun member tag => false;
     lora_member_removed = fun tag => false;
     lora_capability_added = fun member required tag => false;
     lora_capability_removed = fun tag => false |}.

op lean_authorization_join
    (left right : lean_observed_remove_authorization) :
    lean_observed_remove_authorization =
  {| lora_member_added = fun member tag =>
       left.`lora_member_added member tag \/
       right.`lora_member_added member tag;
     lora_member_removed = fun tag =>
       left.`lora_member_removed tag \/ right.`lora_member_removed tag;
     lora_capability_added = fun member required tag =>
       left.`lora_capability_added member required tag \/
       right.`lora_capability_added member required tag;
     lora_capability_removed = fun tag =>
       left.`lora_capability_removed tag \/
       right.`lora_capability_removed tag |}.

op lean_membership_grant_delta
    (target : principal)
    (tag : member_tag) : lean_observed_remove_authorization =
  {| lora_member_added = fun member candidate_tag =>
       member = target /\ candidate_tag = tag;
     lora_member_removed = fun candidate_tag => false;
     lora_capability_added = fun member required candidate_tag => false;
     lora_capability_removed = fun candidate_tag => false |}.

op lean_membership_revoke_delta
    (observed : member_tag fset) : lean_observed_remove_authorization =
  {| lora_member_added = fun member tag => false;
     lora_member_removed = fun tag => tag \in observed;
     lora_capability_added = fun member required tag => false;
     lora_capability_removed = fun tag => false |}.

op lean_capability_grant_delta
    (target : principal)
    (required : capability)
    (tag : capability_tag) : lean_observed_remove_authorization =
  {| lora_member_added = fun member candidate_tag => false;
     lora_member_removed = fun candidate_tag => false;
     lora_capability_added = fun member candidate_required candidate_tag =>
       member = target /\ candidate_required = required /\ candidate_tag = tag;
     lora_capability_removed = fun candidate_tag => false |}.

op lean_capability_revoke_delta
    (observed : capability_tag fset) : lean_observed_remove_authorization =
  {| lora_member_added = fun member tag => false;
     lora_member_removed = fun tag => false;
     lora_capability_added = fun member required tag => false;
     lora_capability_removed = fun tag => tag \in observed |}.

op lean_authorization_delta_of_fact_kind
    (kind : authorization_fact_kind)
    (fact : authorization_fact) : lean_observed_remove_authorization =
  with kind = GenesisMembership =>
    lean_membership_grant_delta
      (oget fact.`af_target) (oget fact.`af_member_tag)
  with kind = MembershipGrant =>
    lean_membership_grant_delta
      (oget fact.`af_target) (oget fact.`af_member_tag)
  with kind = MembershipRevoke =>
    lean_membership_revoke_delta fact.`af_observed_member_tags
  with kind = GenesisCapability =>
    lean_capability_grant_delta
      (oget fact.`af_target)
      (oget fact.`af_capability)
      (oget fact.`af_capability_tag)
  with kind = CapabilityGrant =>
    lean_capability_grant_delta
      (oget fact.`af_target)
      (oget fact.`af_capability)
      (oget fact.`af_capability_tag)
  with kind = CapabilityRevoke =>
    lean_capability_revoke_delta fact.`af_observed_capability_tags.

op lean_authorization_delta_of_fact
    (fact : authorization_fact) : lean_observed_remove_authorization =
  lean_authorization_delta_of_fact_kind fact.`af_kind fact.

op lean_apply_signed_authorization_facts_from
    (current : lean_observed_remove_authorization)
    (facts : signed_authorization_fact list) :
    lean_observed_remove_authorization =
  with facts = [] => current
  with facts = signed_fact :: rest =>
    lean_apply_signed_authorization_facts_from
      (lean_authorization_join current
        (lean_authorization_delta_of_fact signed_fact.`saf_fact))
      rest.

op lean_apply_signed_authorization_facts
    (facts : signed_authorization_fact list) :
    lean_observed_remove_authorization =
  lean_apply_signed_authorization_facts_from lean_authorization_empty facts.

pred lean_authorization_equiv
    (left right : lean_observed_remove_authorization) =
     (forall member tag,
        left.`lora_member_added member tag =
          right.`lora_member_added member tag)
  /\ (forall tag,
        left.`lora_member_removed tag = right.`lora_member_removed tag)
  /\ (forall member required tag,
        left.`lora_capability_added member required tag =
          right.`lora_capability_added member required tag)
  /\ (forall tag,
        left.`lora_capability_removed tag =
          right.`lora_capability_removed tag).

lemma lean_empty_represents_empty_authorization :
  authorization_state_represents_lean
    empty_authorization_state lean_authorization_empty.
proof.
  rewrite /authorization_state_represents_lean /empty_authorization_state
    /lean_authorization_empty.
  smt(in_fset0).
qed.

lemma successful_fact_application_represents_lean_delta
    (current context_state next : authorization_state)
    (creator : principal)
    (fact : authorization_fact) :
  apply_authorization_fact current context_state creator fact = Some next =>
  authorization_state_represents_lean
    next
    (lean_authorization_join
      (project_authorization_state current)
      (lean_authorization_delta_of_fact fact)).
proof.
  move=> applied.
  rewrite /apply_authorization_fact in applied.
  case: (! authorization_fact_shape_valid fact \/
         fact.`af_id \in current.`as_fact_ids \/
         ! authorization_issuer_allowed current context_state creator fact)
    applied=> //= applied.
  case: fact.`af_kind applied => /= applied.
  + case: (member_tag_known current (oget fact.`af_member_tag) \/
           oget fact.`af_target \in current.`as_retired_principals)
      applied=> //= applied.
    rewrite /authorization_state_represents_lean /lean_authorization_join
      /project_authorization_state /lean_authorization_delta_of_fact
      /lean_authorization_delta_of_fact_kind /lean_membership_grant_delta.
    smt(in_fsetU in_fset1).
  + case: (capability_tag_known current (oget fact.`af_capability_tag))
      applied=> //= applied.
    rewrite /authorization_state_represents_lean /lean_authorization_join
      /project_authorization_state /lean_authorization_delta_of_fact
      /lean_authorization_delta_of_fact_kind /lean_capability_grant_delta.
    smt(in_fsetU in_fset1).
  + case: (member_tag_known current (oget fact.`af_member_tag) \/
           oget fact.`af_target \in current.`as_retired_principals)
      applied=> //= applied.
    rewrite /authorization_state_represents_lean /lean_authorization_join
      /project_authorization_state /lean_authorization_delta_of_fact
      /lean_authorization_delta_of_fact_kind /lean_membership_grant_delta.
    smt(in_fsetU in_fset1).
  + case: (! all_member_tags_known current
             (elems fact.`af_observed_member_tags)) applied=> //= applied.
    rewrite /authorization_state_represents_lean /lean_authorization_join
      /project_authorization_state /lean_authorization_delta_of_fact
      /lean_authorization_delta_of_fact_kind /lean_membership_revoke_delta.
    smt(in_fsetU).
  + case: (capability_tag_known current (oget fact.`af_capability_tag))
      applied=> //= applied.
    rewrite /authorization_state_represents_lean /lean_authorization_join
      /project_authorization_state /lean_authorization_delta_of_fact
      /lean_authorization_delta_of_fact_kind /lean_capability_grant_delta.
    smt(in_fsetU in_fset1).
  + case: (! all_capability_tags_known current
             (elems fact.`af_observed_capability_tags)) applied=> //= applied.
    rewrite /authorization_state_represents_lean /lean_authorization_join
      /project_authorization_state /lean_authorization_delta_of_fact
      /lean_authorization_delta_of_fact_kind /lean_capability_revoke_delta.
    smt(in_fsetU).
qed.
