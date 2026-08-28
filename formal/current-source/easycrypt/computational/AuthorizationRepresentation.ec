require import AllCore List FSet.
require import ProtocolTypes CanonicalEncoding AuthorizationState AuthorizationAncestry.

(* Representation mapping for the observed-remove authorization mathematics.

   Lean source closure:
     formal/current-source/CausalDagCgka/Authorization.lean
     blob 55b138aa423f46db69d50d4427d89d67636c6281

   Full checked Lean source closure SHA-256:
     bdee462415deb6abed681e807f4f0d12cfa4472527c7fa4dc8b86d9a62ee6286

   The Lean [AuthState] representation is predicate-valued: immutable add
   facts and remove tombstones.  The executable EasyCrypt normalizer stores
   finite sets of the same facts.  This file states the mapping explicitly
   and proves that active membership and capability queries are identical
   under production's exact-incarnation equality. *)

type lean_observed_remove_authorization = {
  lora_member_added : principal -> member_tag -> bool;
  lora_member_removed : member_tag -> bool;
  lora_capability_added : principal -> capability -> capability_tag -> bool;
  lora_capability_removed : capability_tag -> bool
}.

op project_authorization_state
    (state : authorization_state) : lean_observed_remove_authorization =
  {| lora_member_added =
       fun member tag =>
         exists entry,
              entry \in state.`as_member_grants
           /\ entry.`mge_principal = member
           /\ entry.`mge_tag = tag;
     lora_member_removed =
       fun tag => tag \in state.`as_removed_member_tags;
     lora_capability_added =
       fun member required tag =>
         exists entry,
              entry \in state.`as_capability_grants
           /\ entry.`cge_principal = member
           /\ entry.`cge_capability = required
           /\ entry.`cge_tag = tag;
     lora_capability_removed =
       fun tag => tag \in state.`as_removed_capability_tags |}.

pred authorization_state_represents_lean
    (state : authorization_state)
    (model : lean_observed_remove_authorization) =
     (forall member tag,
        model.`lora_member_added member tag =
          (exists entry,
               entry \in state.`as_member_grants
            /\ entry.`mge_principal = member
            /\ entry.`mge_tag = tag))
  /\ (forall tag,
        model.`lora_member_removed tag =
          (tag \in state.`as_removed_member_tags))
  /\ (forall member required tag,
        model.`lora_capability_added member required tag =
          (exists entry,
               entry \in state.`as_capability_grants
            /\ entry.`cge_principal = member
            /\ entry.`cge_capability = required
            /\ entry.`cge_tag = tag))
  /\ (forall tag,
        model.`lora_capability_removed tag =
          (tag \in state.`as_removed_capability_tags)).

pred lean_member_active
    (model : lean_observed_remove_authorization)
    (member : principal) =
  exists tag,
       model.`lora_member_added member tag
    /\ ! model.`lora_member_removed tag.

pred lean_capability_active
    (model : lean_observed_remove_authorization)
    (member : principal)
    (required : capability) =
  exists tag,
       model.`lora_capability_added member required tag
    /\ ! model.`lora_capability_removed tag.

lemma project_authorization_state_represents
    (state : authorization_state) :
  authorization_state_represents_lean
    state (project_authorization_state state).
proof.
  by rewrite /authorization_state_represents_lean
    /project_authorization_state.
qed.

lemma projected_member_active_is_exact
    (state : authorization_state)
    (member : principal) :
  lean_member_active (project_authorization_state state) member <=>
  member_active Production state member.
proof.
  rewrite /lean_member_active /project_authorization_state
    /member_active /principal_matches /defense_enabled.
  smt().
qed.

lemma projected_capability_active_is_exact
    (state : authorization_state)
    (member : principal)
    (required : capability) :
  lean_capability_active
      (project_authorization_state state) member required <=>
  capability_active Production state member required.
proof.
  rewrite /lean_capability_active /project_authorization_state
    /capability_active /principal_matches /defense_enabled.
  smt().
qed.

pred lean_observed_remove_state_of_facts
    (creator : principal)
    (facts : signed_authorization_fact list)
    (model : lean_observed_remove_authorization) =
  exists state,
       authorization_policy_replay creator facts = Some state
    /\ model = project_authorization_state state.

lemma policy_replay_has_observed_remove_projection
    (creator : principal)
    (facts : signed_authorization_fact list)
    (state : authorization_state) :
  authorization_policy_replay creator facts = Some state =>
  lean_observed_remove_state_of_facts
    creator facts (project_authorization_state state).
proof.
  by move=> replay; exists state.
qed.

lemma policy_ancestry_has_observed_remove_projection
    (creator : principal)
    (facts : signed_authorization_fact list)
    (state : authorization_state) :
  authorization_ancestry_valid creator facts state =>
  lean_observed_remove_state_of_facts
    creator facts (project_authorization_state state).
proof.
  rewrite /authorization_ancestry_valid.
  exact (policy_replay_has_observed_remove_projection creator facts state).
qed.
