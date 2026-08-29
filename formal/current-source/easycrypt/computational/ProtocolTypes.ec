require import AllCore List FSet.

(* Concrete wrapper carriers keep mutation witnesses executable while the
   cryptographic algorithms remain module parameters. *)
type protocol_domain = [ ProtocolDomain of int ].
type document_id = [ DocumentId of int ].
type operation_id = [ OperationId of int ].
type verification_key = [ VerificationKey of int ].
type incarnation_nonce = [ IncarnationNonce of int ].
type node_id = [ NodeId of int ].
type fact_id = [ FactId of int ].
type nonce = [ Nonce of int ].
type payload = [ Payload of int ].
type leaf_key = [ LeafKey of int ].
type member_tag = [ MemberTag of int ].
type capability_tag = [ CapabilityTag of int ].
type raw_bytes = [ RawBytes of int ].
type beekem_path = [ BeeKemPath of int ].
type merge_node = [ MergeNode of int ].
type segment_id = [ SegmentId of int ].
type path_bits = [ PathBits of int ].

type principal = {
  p_verification_key : verification_key;
  p_incarnation_nonce : incarnation_nonce
}.

type capability = [
  | CapEdit
  | CapAdmin
  | CapHistoryGrant
  | CapPuncture
  | CapBeeKemUpdate
].

(* The authorization state is public protocol data.  It lives in the shared
   type layer so the abstract authorization digest can carry the complete
   normalized state rather than only its fact-id projection. *)
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

type authorization_digest = [
  | ExactAuthorizationDigest of authorization_state
  | AuthorizationDigest of int
  | InvalidAuthorizationDigest of int
].

type operation_kind = [
  | OpEdit
  | OpAddMember
  | OpRemoveMember
  | OpGrantCapability
  | OpRevokeCapability
  | OpBeeKemUpdate
  | OpHistoryGrant
  | OpPuncture
].

type edit_action = [ EditText | DeleteDocument ].

type region_interval = {
  ri_segment : segment_id;
  ri_start : int;
  ri_end : int
}.

type region = region_interval fset.

type subtree_cover_entry = {
  sce_segment : segment_id;
  sce_path : path_bits;
  sce_depth : int
}.

type segment_cover = subtree_cover_entry fset.

type operation_body = [
  | EditBody of edit_action & payload
  | AddMemberBody of principal & leaf_key
  | RemoveMemberBody of principal & member_tag fset & capability_tag fset
  | GrantCapabilityBody of principal & capability & capability_tag
  | RevokeCapabilityBody of capability_tag fset
  | BeeKemUpdateBody of principal & beekem_path
  | HistoryGrantBody of principal & merge_node & region & segment_cover
  | PunctureBody of region
  | OpaqueBody of raw_bytes
].

type operation_envelope = {
  oe_protocol_domain : protocol_domain;
  oe_protocol_version : int;
  oe_document_id : document_id;
  oe_operation_id : operation_id;
  oe_author : principal;
  oe_required_capability : capability;
  oe_direct_predecessors : node_id fset;
  oe_authorization_digest : authorization_digest;
  oe_operation_kind : operation_kind;
  oe_operation_body : operation_body;
  oe_nonce : nonce
}.

type authorization_fact_kind = [
  | GenesisMembership
  | GenesisCapability
  | MembershipGrant
  | MembershipRevoke
  | CapabilityGrant
  | CapabilityRevoke
].

type authorization_fact = {
  af_id : fact_id;
  af_kind : authorization_fact_kind;
  af_issuer : principal;
  af_context : fact_id fset;
  af_target : principal option;
  af_capability : capability option;
  af_member_tag : member_tag option;
  af_capability_tag : capability_tag option;
  af_observed_member_tags : member_tag fset;
  af_observed_capability_tags : capability_tag fset
}.

type history_grant = {
  hg_issuer : principal;
  hg_recipient : principal;
  hg_merge_node : merge_node;
  hg_region : region;
  hg_cover : segment_cover;
  hg_context : fact_id fset;
  hg_protocol_version : int
}.

type puncture = {
  pu_issuer : principal;
  pu_region : region;
  pu_context : fact_id fset
}.

type transcript_label = [ ProtocolOperationTranscript ].

type operation_transcript = {
  ot_label : transcript_label;
  ot_protocol_version : int;
  ot_document_id : document_id;
  ot_operation_id : operation_id;
  ot_author_verification_key : verification_key;
  ot_author_incarnation_nonce : incarnation_nonce;
  ot_required_capability : capability option;
  ot_direct_predecessors : node_id fset;
  ot_authorization_digest : authorization_digest;
  ot_operation_kind : operation_kind;
  ot_operation_body : operation_body option;
  ot_nonce : nonce
}.

type signature_message = [
  | OperationSignatureMessage of operation_transcript
  | AuthorizationFactSignatureMessage of authorization_fact
].

(* The executable witness signature contains the exact signed message rather
   than an abstract integer code. This makes transcript mutations deterministic
   and keeps the author-key check separate from transcript equality. *)
type signature_bytes = [ SignatureBytes of signature_message ].

type signature = {
  sig_verification_key : verification_key;
  sig_bytes : signature_bytes
}.

type accepted_operation = {
  ao_operation_id : operation_id;
  ao_author : principal;
  ao_capability : capability;
  ao_context : fact_id fset;
  ao_transcript : operation_transcript
}.

type history_expectation = {
  he_issuer : principal;
  he_recipient : principal;
  he_merge_node : merge_node;
  he_region : region;
  he_cover : segment_cover
}.

type closure_map = node_id -> fact_id fset option.
type fact_content_map = fact_id -> authorization_fact option.
type beekem_path_map = node_id fset -> beekem_path option.

type protocol_state = {
  ps_creator : principal;
  ps_document_id : document_id;
  ps_nodes : node_id fset;
  ps_closures : closure_map;
  ps_fact_contents : fact_content_map;
  ps_seen_operation_ids : operation_id fset;
  ps_seen_nonces : nonce fset;
  ps_beekem_paths : beekem_path_map;
  ps_history_expectation : history_expectation option;
  ps_expected_puncture_regions : region fset
}.

type defense = [
  | DefenseCanonicalEncoding
  | DefenseDomainVersion
  | DefenseDocumentBinding
  | DefenseFreshness
  | DefensePredecessorCompleteness
  | DefenseExactCausalContext
  | DefenseAuthorizationDigest
  | DefenseOperationSignature
  | DefenseAuthorKeyBinding
  | DefenseIncarnationBinding
  | DefenseOperationBodyPolicy
  | DefenseOperationBodyBinding
  | DefenseRequiredCapabilityBinding
  | DefenseAddTargetFreshness
  | DefenseBeeKemPath
  | DefenseGrantRecipientBinding
  | DefenseMergeNodeBinding
  | DefenseRegionBinding
  | DefenseSegmentBinding
  | DefensePuncturePolicy
].

type validator_mode = [ Production | WithoutDefense of defense ].

op defense_enabled (mode : validator_mode) (d : defense) : bool =
  with mode = Production => true
  with mode = WithoutDefense removed => removed <> d.

type validation_failure = [
  | FailureCanonicalDecoding
  | FailureCanonicalReencoding
  | FailureDomainVersion
  | FailureDocumentBinding
  | FailureFreshness
  | FailureMissingPredecessor
  | FailurePredecessorCompleteness
  | FailureExactCausalContext
  | FailureAuthorizationFacts
  | FailureAuthorizationDigest
  | FailureAuthorKeyBinding
  | FailureOperationSignature
  | FailureActiveIncarnation
  | FailureRequiredCapabilityActive
  | FailureRequiredCapabilityBinding
  | FailureOperationBodyPolicy
  | FailureAddTarget
  | FailureAddTargetFreshness
  | FailureBeeKemPath
  | FailureHistoryEncoding
  | FailureHistoryExpectation
  | FailureGrantRecipientBinding
  | FailureMergeNodeBinding
  | FailureRegionBinding
  | FailureSegmentBinding
  | FailurePuncturePolicy
].

type validation_result = {
  vr_accepted : bool;
  vr_failure : validation_failure option
}.

op validation_success : validation_result =
  {| vr_accepted = true; vr_failure = None |}.

op validation_error (failure : validation_failure) : validation_result =
  {| vr_accepted = false; vr_failure = Some failure |}.
