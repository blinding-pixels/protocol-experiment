require import AllCore List FSet.
require import ProtocolTypes CanonicalEncoding ProtocolPrimitives.

(* Representation mapping source:
   blinding-pixels/Facets@7f685d35a72a463cbcc1052a81710bb02c0c5b80
   CausalDagCgka/Authorization.lean blob
   55b138aa423f46db69d50d4427d89d67636c6281. *)

type member_grant_entry = {
  mge_tag : member_tag;
  mge_principal : principal
}.

type capability_grant_entry = {
  cge_tag : capability_tag;
  cge_principal : principal;
  cge_capability : capability
}.

type authorization_state = {
  as_member_grants : member_grant_entry fset;
  as_removed_member_tags : member_tag fset;
  as_capability_grants : capability_grant_entry fset;
  as_removed_capability_tags : capability_tag fset;
  as_retired_principals : principal fset;
  as_fact_ids : fact_id fset
}.

type authorization_snapshot = {
  snapshot_context : fact_id fset;
  snapshot_state : authorization_state
}.

op empty_authorization_state : authorization_state =
  {| as_member_grants = fset0;
     as_removed_member_tags = fset0;
     as_capability_grants = fset0;
     as_removed_capability_tags = fset0;
     as_retired_principals = fset0;
     as_fact_ids = fset0 |}.

op principal_matches
    (mode : validator_mode)
    (expected observed : principal) : bool =
  if defense_enabled mode DefenseIncarnationBinding
  then expected = observed
  else expected.`p_verification_key = observed.`p_verification_key.

op member_active
    (mode : validator_mode)
    (state : authorization_state)
    (candidate : principal) : bool =
  exists entry,
       entry \in state.`as_member_grants
    /\ entry.`mge_tag \notin state.`as_removed_member_tags
    /\ principal_matches mode candidate entry.`mge_principal.

op capability_active
    (mode : validator_mode)
    (state : authorization_state)
    (candidate : principal)
    (required : capability) : bool =
  exists entry,
       entry \in state.`as_capability_grants
    /\ entry.`cge_tag \notin state.`as_removed_capability_tags
    /\ principal_matches mode candidate entry.`cge_principal
    /\ entry.`cge_capability = required.

op member_tag_known
    (state : authorization_state)
    (tag : member_tag) : bool =
  exists entry,
    entry \in state.`as_member_grants /\ entry.`mge_tag = tag.

op capability_tag_known
    (state : authorization_state)
    (tag : capability_tag) : bool =
  exists entry,
    entry \in state.`as_capability_grants /\ entry.`cge_tag = tag.

op member_principal_for_tag_list
    (entries : member_grant_entry list)
    (tag : member_tag) : principal option =
  with entries = [] => None
  with entries = entry :: rest =>
    if entry.`mge_tag = tag
    then Some entry.`mge_principal
    else member_principal_for_tag_list rest tag.

op member_principal_for_tag
    (state : authorization_state)
    (tag : member_tag) : principal option =
  member_principal_for_tag_list (elems state.`as_member_grants) tag.

op all_member_tags_known
    (state : authorization_state)
    (tags : member_tag list) : bool =
  with tags = [] => true
  with tags = tag :: rest =>
    member_tag_known state tag /\ all_member_tags_known state rest.

op all_capability_tags_known
    (state : authorization_state)
    (tags : capability_tag list) : bool =
  with tags = [] => true
  with tags = tag :: rest =>
    capability_tag_known state tag /\ all_capability_tags_known state rest.

op retire_member_tags
    (state : authorization_state)
    (tags : member_tag list)
    (retired : principal fset) : principal fset =
  with tags = [] => retired
  with tags = tag :: rest =>
    let principal_option = member_principal_for_tag state tag in
    let next_retired =
      if principal_option = None
      then retired
      else retired `|` fset1 (oget principal_option) in
    retire_member_tags state rest next_retired.

op membership_principal_seen
    (state : authorization_state)
    (candidate : principal) : bool =
  exists entry,
    entry \in state.`as_member_grants /\ entry.`mge_principal = candidate.

op incarnation_nonce_seen
    (state : authorization_state)
    (candidate : principal) : bool =
     (exists entry,
        entry \in state.`as_member_grants /\
        entry.`mge_principal.`p_incarnation_nonce =
          candidate.`p_incarnation_nonce)
  \/ (exists retired,
        retired \in state.`as_retired_principals /\
        retired.`p_incarnation_nonce = candidate.`p_incarnation_nonce).

op authorization_snapshot_lookup
    (context : fact_id fset)
    (snapshots : authorization_snapshot list) : authorization_state option =
  with snapshots = [] => None
  with snapshots = snapshot :: rest =>
    if snapshot.`snapshot_context = context
    then Some snapshot.`snapshot_state
    else authorization_snapshot_lookup context rest.

op authorization_fact_shape_valid_kind
    (kind : authorization_fact_kind)
    (fact : authorization_fact) : bool =
  with kind = GenesisMembership =>
       fact.`af_target <> None
    /\ fact.`af_member_tag <> None
    /\ fact.`af_capability = None
    /\ fact.`af_capability_tag = None
    /\ fact.`af_observed_member_tags = fset0
    /\ fact.`af_observed_capability_tags = fset0
  with kind = MembershipGrant =>
       fact.`af_target <> None
    /\ fact.`af_member_tag <> None
    /\ fact.`af_capability = None
    /\ fact.`af_capability_tag = None
    /\ fact.`af_observed_member_tags = fset0
    /\ fact.`af_observed_capability_tags = fset0
  with kind = MembershipRevoke =>
       fact.`af_target = None
    /\ fact.`af_member_tag = None
    /\ fact.`af_capability = None
    /\ fact.`af_capability_tag = None
    /\ fact.`af_observed_member_tags <> fset0
    /\ fact.`af_observed_capability_tags = fset0
  with kind = GenesisCapability =>
       fact.`af_target <> None
    /\ fact.`af_member_tag = None
    /\ fact.`af_capability <> None
    /\ fact.`af_capability_tag <> None
    /\ fact.`af_observed_member_tags = fset0
    /\ fact.`af_observed_capability_tags = fset0
  with kind = CapabilityGrant =>
       fact.`af_target <> None
    /\ fact.`af_member_tag = None
    /\ fact.`af_capability <> None
    /\ fact.`af_capability_tag <> None
    /\ fact.`af_observed_member_tags = fset0
    /\ fact.`af_observed_capability_tags = fset0
  with kind = CapabilityRevoke =>
       fact.`af_target = None
    /\ fact.`af_member_tag = None
    /\ fact.`af_capability = None
    /\ fact.`af_capability_tag = None
    /\ fact.`af_observed_member_tags = fset0
    /\ fact.`af_observed_capability_tags <> fset0.

op authorization_fact_shape_valid (fact : authorization_fact) : bool =
  authorization_fact_shape_valid_kind fact.`af_kind fact.

op genesis_authorization_fact (fact : authorization_fact) : bool =
  fact.`af_kind = GenesisMembership \/ fact.`af_kind = GenesisCapability.

op authorization_issuer_allowed
    (current context_state : authorization_state)
    (creator : principal)
    (fact : authorization_fact) : bool =
  if genesis_authorization_fact fact
  then fact.`af_issuer = creator /\ fact.`af_context = current.`as_fact_ids
  else
       member_active Production context_state fact.`af_issuer
    /\ capability_active Production context_state fact.`af_issuer CapAdmin.

op apply_authorization_fact_kind
    (kind : authorization_fact_kind)
    (current : authorization_state)
    (fact : authorization_fact) : authorization_state option =
  with kind = GenesisMembership =>
    let target = oget fact.`af_target in
    let tag = oget fact.`af_member_tag in
    if member_tag_known current tag
       \/ target \in current.`as_retired_principals
    then None
    else Some
      {| current with
         as_member_grants =
           current.`as_member_grants `|`
           fset1 {| mge_tag = tag; mge_principal = target |};
         as_fact_ids = current.`as_fact_ids `|` fset1 fact.`af_id |}
  with kind = MembershipGrant =>
    let target = oget fact.`af_target in
    let tag = oget fact.`af_member_tag in
    if member_tag_known current tag
       \/ target \in current.`as_retired_principals
    then None
    else Some
      {| current with
         as_member_grants =
           current.`as_member_grants `|`
           fset1 {| mge_tag = tag; mge_principal = target |};
         as_fact_ids = current.`as_fact_ids `|` fset1 fact.`af_id |}
  with kind = MembershipRevoke =>
    if ! all_member_tags_known current
           (elems fact.`af_observed_member_tags)
    then None
    else Some
      {| current with
         as_removed_member_tags =
           current.`as_removed_member_tags `|`
           fact.`af_observed_member_tags;
         as_retired_principals =
           retire_member_tags current
             (elems fact.`af_observed_member_tags)
             current.`as_retired_principals;
         as_fact_ids = current.`as_fact_ids `|` fset1 fact.`af_id |}
  with kind = GenesisCapability =>
    let target = oget fact.`af_target in
    let required = oget fact.`af_capability in
    let tag = oget fact.`af_capability_tag in
    if capability_tag_known current tag
    then None
    else Some
      {| current with
         as_capability_grants =
           current.`as_capability_grants `|`
           fset1
             {| cge_tag = tag;
                cge_principal = target;
                cge_capability = required |};
         as_fact_ids = current.`as_fact_ids `|` fset1 fact.`af_id |}
  with kind = CapabilityGrant =>
    let target = oget fact.`af_target in
    let required = oget fact.`af_capability in
    let tag = oget fact.`af_capability_tag in
    if capability_tag_known current tag
    then None
    else Some
      {| current with
         as_capability_grants =
           current.`as_capability_grants `|`
           fset1
             {| cge_tag = tag;
                cge_principal = target;
                cge_capability = required |};
         as_fact_ids = current.`as_fact_ids `|` fset1 fact.`af_id |}
  with kind = CapabilityRevoke =>
    if ! all_capability_tags_known current
           (elems fact.`af_observed_capability_tags)
    then None
    else Some
      {| current with
         as_removed_capability_tags =
           current.`as_removed_capability_tags `|`
           fact.`af_observed_capability_tags;
         as_fact_ids = current.`as_fact_ids `|` fset1 fact.`af_id |}.

op apply_authorization_fact
    (current context_state : authorization_state)
    (creator : principal)
    (fact : authorization_fact) : authorization_state option =
  if ! authorization_fact_shape_valid fact
     \/ fact.`af_id \in current.`as_fact_ids
     \/ ! authorization_issuer_allowed current context_state creator fact
  then None
  else apply_authorization_fact_kind fact.`af_kind current fact.

(* At the EasyCrypt abstraction boundary the authorization digest is the
   canonical fact-id set itself, not an unconstrained integer code.  Combined
   with immutable fact-content binding and deterministic policy replay, this
   makes the digest an injective name for the accepted causal authorization
   input.  Concrete Rust byte hashing remains a correspondence obligation. *)
op authorization_digest_of
    (state : authorization_state) : authorization_digest =
  ExactAuthorizationDigest state.`as_fact_ids.

lemma authorization_digest_of_context_injective
    (left right : authorization_state) :
  authorization_digest_of left = authorization_digest_of right =>
  left.`as_fact_ids = right.`as_fact_ids.
proof.
  by rewrite /authorization_digest_of.
qed.

module NormalizeAuthorization(S : SIGNATURE_SCHEME) = {
  proc normalize(
    facts : signed_authorization_fact list,
    creator : principal
  ) : bool * authorization_state = {
    var valid : bool;
    var current : authorization_state;
    var snapshots : authorization_snapshot list;
    var remaining : signed_authorization_fact list;
    var signed_fact : signed_authorization_fact;
    var fact : authorization_fact;
    var sig : signature;
    var signature_valid : bool;
    var context_state : authorization_state option;
    var next_state : authorization_state option;

    valid <- true;
    current <- empty_authorization_state;
    snapshots <-
      [{| snapshot_context = fset0;
          snapshot_state = empty_authorization_state |}];
    remaining <- facts;

    while (valid /\ remaining <> []) {
      signed_fact <- head witness remaining;
      remaining <- behead remaining;
      fact <- signed_fact.`saf_fact;
      sig <- signed_fact.`saf_signature;

      signature_valid <@ S.verify(
        sig.`sig_verification_key,
        fact_signature_message fact,
        sig.`sig_bytes
      );

      if (! signature_valid \/
          sig.`sig_verification_key <>
            fact.`af_issuer.`p_verification_key) {
        valid <- false;
      }

      if (valid) {
        context_state <-
          authorization_snapshot_lookup fact.`af_context snapshots;
        if (context_state = None) {
          valid <- false;
        } else {
          next_state <-
            apply_authorization_fact current (oget context_state) creator fact;
          if (next_state = None) {
            valid <- false;
          } else {
            current <- oget next_state;
            snapshots <- rcons snapshots
              {| snapshot_context = current.`as_fact_ids;
                 snapshot_state = current |};
          }
        }
      }
    }

    return (valid, current);
  }
}.

lemma production_principal_matching_is_exact
    (p q : principal) :
  principal_matches Production p q = (p = q).
proof. by rewrite /principal_matches /defense_enabled. qed.

lemma removed_incarnation_defense_matches_by_key
    (p q : principal) :
  principal_matches
    (WithoutDefense DefenseIncarnationBinding) p q =
  (p.`p_verification_key = q.`p_verification_key).
proof. by rewrite /principal_matches /defense_enabled. qed.
