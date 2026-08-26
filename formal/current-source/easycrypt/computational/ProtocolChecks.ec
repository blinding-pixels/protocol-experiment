require import AllCore List FSet.
require import ProtocolTypes CanonicalEncoding PrimitiveGames AuthorizationState.

op expected_protocol_domain : protocol_domain = ProtocolDomain 1.
op expected_protocol_version : int = 1.

op fact_ids_of_signed_facts
    (facts : signed_authorization_fact list) : fact_id fset =
  with facts = [] => fset0
  with facts = signed_fact :: rest =>
    fset1 signed_fact.saf_fact.af_id `|` fact_ids_of_signed_facts rest.

op signed_facts_for_ids
    (facts : signed_authorization_fact list)
    (ids : fact_id fset) : signed_authorization_fact list =
  with facts = [] => []
  with facts = signed_fact :: rest =>
    if signed_fact.saf_fact.af_id \in ids
    then signed_fact :: signed_facts_for_ids rest ids
    else signed_facts_for_ids rest ids.

op all_predecessors_exist_list
    (nodes : node_id fset)
    (predecessors : node_id list) : bool =
  with predecessors = [] => true
  with predecessors = predecessor :: rest =>
    predecessor \in nodes /\ all_predecessors_exist_list nodes rest.

op all_predecessors_exist
    (state : protocol_state)
    (predecessors : node_id fset) : bool =
  all_predecessors_exist_list state.ps_nodes (elems predecessors).

op closure_union_list
    (closures : closure_map)
    (predecessors : node_id list) : fact_id fset option =
  with predecessors = [] => Some fset0
  with predecessors = predecessor :: rest =>
    let here = closures predecessor in
    let tail = closure_union_list closures rest in
    if here = None \/ tail = None
    then None
    else Some (oget here `|` oget tail).

op exact_predecessor_closure
    (state : protocol_state)
    (predecessors : node_id fset) : fact_id fset option =
  closure_union_list state.ps_closures (elems predecessors).

op region_intervals_valid_list
    (intervals : region_interval list) : bool =
  with intervals = [] => true
  with intervals = interval :: rest =>
       0 <= interval.ri_start
    /\ interval.ri_start < interval.ri_end
    /\ region_intervals_valid_list rest.

op region_valid (selected : region) : bool =
  region_intervals_valid_list (elems selected).

op cover_entries_valid_list
    (entries : subtree_cover_entry list) : bool =
  with entries = [] => true
  with entries = entry :: rest =>
    0 <= entry.sce_depth /\ cover_entries_valid_list rest.

op segment_in_region
    (segment : segment_id)
    (selected : region) : bool =
  exists interval,
    interval \in selected /\ interval.ri_segment = segment.

op cover_segments_within_region_list
    (entries : subtree_cover_entry list)
    (selected : region) : bool =
  with entries = [] => true
  with entries = entry :: rest =>
       segment_in_region entry.sce_segment selected
    /\ cover_segments_within_region_list rest selected.

op cover_valid_for_region
    (cover : segment_cover)
    (selected : region) : bool =
     cover_entries_valid_list (elems cover)
  /\ cover_segments_within_region_list (elems cover) selected.

op operation_body_kind (body : operation_body) : operation_kind option =
  with body = EditBody action content => Some OpEdit
  with body = AddMemberBody target leaf => Some OpAddMember
  with body = RemoveMemberBody target member_tags capability_tags =>
    Some OpRemoveMember
  with body = GrantCapabilityBody target required tag =>
    Some OpGrantCapability
  with body = RevokeCapabilityBody tags => Some OpRevokeCapability
  with body = BeeKemUpdateBody author path => Some OpBeeKemUpdate
  with body = HistoryGrantBody recipient merge selected cover =>
    Some OpHistoryGrant
  with body = PunctureBody selected => Some OpPuncture
  with body = OpaqueBody bytes => None.

op operation_body_valid (body : operation_body) : bool =
  with body = EditBody action content => true
  with body = AddMemberBody target leaf => true
  with body = RemoveMemberBody target member_tags capability_tags =>
    member_tags <> fset0
  with body = GrantCapabilityBody target required tag => true
  with body = RevokeCapabilityBody tags => tags <> fset0
  with body = BeeKemUpdateBody author path => true
  with body = HistoryGrantBody recipient merge selected cover =>
    region_valid selected /\ cover_entries_valid_list (elems cover)
  with body = PunctureBody selected => region_valid selected
  with body = OpaqueBody bytes => false.

op operation_body_valid_for_envelope
    (envelope : operation_envelope) : bool =
     operation_body_kind envelope.oe_operation_body =
       Some envelope.oe_operation_kind
  /\ operation_body_valid envelope.oe_operation_body.

op required_capability_for_operation
    (kind : operation_kind)
    (body : operation_body) : capability =
  with kind = OpEdit, body = EditBody DeleteDocument content => CapAdmin
  with kind = OpEdit, body = _ => CapEdit
  with kind = OpAddMember, body = _ => CapAdmin
  with kind = OpRemoveMember, body = _ => CapAdmin
  with kind = OpGrantCapability, body = _ => CapAdmin
  with kind = OpRevokeCapability, body = _ => CapAdmin
  with kind = OpBeeKemUpdate, body = _ => CapBeeKemUpdate
  with kind = OpHistoryGrant, body = _ => CapHistoryGrant
  with kind = OpPuncture, body = _ => CapPuncture.

op add_target_of_body (body : operation_body) : principal option =
  with body = AddMemberBody target leaf => Some target
  with body = _ => None.

op add_target_fresh
    (state : authorization_state)
    (target : principal) : bool =
     ! membership_principal_seen state target
  /\ target \notin state.as_retired_principals
  /\ ! incarnation_nonce_seen state target.

op beekem_update_valid_body
    (state : protocol_state)
    (envelope : operation_envelope)
    (body : operation_body) : bool =
  with body = BeeKemUpdateBody body_author path =>
       body_author = envelope.oe_author
    /\ state.ps_beekem_paths envelope.oe_direct_predecessors = Some path
  with body = _ => false.

op beekem_update_valid
    (state : protocol_state)
    (envelope : operation_envelope) : bool =
  beekem_update_valid_body state envelope envelope.oe_operation_body.

op history_recipient_of_body (body : operation_body) : principal option =
  with body = HistoryGrantBody recipient merge selected cover => Some recipient
  with body = _ => None.

op history_merge_node_of_body (body : operation_body) : merge_node option =
  with body = HistoryGrantBody recipient merge selected cover => Some merge
  with body = _ => None.

op history_region_of_body (body : operation_body) : region option =
  with body = HistoryGrantBody recipient merge selected cover => Some selected
  with body = _ => None.

op history_cover_of_body (body : operation_body) : segment_cover option =
  with body = HistoryGrantBody recipient merge selected cover => Some cover
  with body = _ => None.

op puncture_region_of_body (body : operation_body) : region option =
  with body = PunctureBody selected => Some selected
  with body = _ => None.

op puncture_binding_valid
    (mode : validator_mode)
    (state : protocol_state)
    (envelope : operation_envelope) : bool =
  if ! defense_enabled mode DefensePuncturePolicy
  then true
  else
    let selected = puncture_region_of_body envelope.oe_operation_body in
       selected <> None
    /\ envelope.oe_required_capability = CapPuncture
    /\ oget selected \in state.ps_expected_puncture_regions.

op closure_map_insert
    (closures : closure_map)
    (node : node_id)
    (context : fact_id fset) : closure_map =
  fun candidate =>
    if candidate = node then Some context else closures candidate.

op protocol_state_after_acceptance
    (state : protocol_state)
    (envelope : operation_envelope)
    (node : node_id)
    (context : fact_id fset) : protocol_state =
  {| state with
     ps_nodes = state.ps_nodes `|` fset1 node;
     ps_closures = closure_map_insert state.ps_closures node context;
     ps_seen_operation_ids =
       state.ps_seen_operation_ids `|` fset1 envelope.oe_operation_id;
     ps_seen_nonces = state.ps_seen_nonces `|` fset1 envelope.oe_nonce |}.
