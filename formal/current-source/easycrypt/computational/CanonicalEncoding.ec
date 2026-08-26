require import AllCore List FSet.
require import ProtocolTypes.

(* The raw-wire datatype separates malformed, decodable noncanonical, and
   canonical byte strings. This is the EasyCrypt-level encoding contract; Rust
   byte-for-byte correspondence remains an external test obligation. *)
type raw_operation = [
  | CanonicalWire of operation_envelope
  | NonCanonicalWire of operation_envelope & raw_bytes
  | MalformedWire of raw_bytes
].

type signed_operation = {
  so_raw : raw_operation;
  so_signature : signature
}.

type signed_authorization_fact = {
  saf_fact : authorization_fact;
  saf_signature : signature
}.

type public_view = {
  pv_facts : signed_authorization_fact list;
  pv_observed_fact_ids : fact_id fset
}.

type node_material = {
  nm_transcript : operation_transcript;
  nm_signature : signature
}.

op encode_operation (envelope : operation_envelope) : raw_operation =
  CanonicalWire envelope.

op decode_operation (raw : raw_operation) : operation_envelope option =
  with raw = CanonicalWire envelope => Some envelope
  with raw = NonCanonicalWire envelope bytes => Some envelope
  with raw = MalformedWire bytes => None.

op canonical_reencoding (raw : raw_operation) : bool =
  with raw = CanonicalWire envelope => true
  with raw = NonCanonicalWire envelope bytes => false
  with raw = MalformedWire bytes => false.

op operation_transcript
    (mode : validator_mode)
    (envelope : operation_envelope) : operation_transcript =
  {| ot_label = ProtocolOperationTranscript;
     ot_protocol_version = envelope.`oe_protocol_version;
     ot_document_id = envelope.`oe_document_id;
     ot_operation_id = envelope.`oe_operation_id;
     ot_author_verification_key = envelope.`oe_author.`p_verification_key;
     ot_author_incarnation_nonce = envelope.`oe_author.`p_incarnation_nonce;
     ot_required_capability =
       if defense_enabled mode DefenseRequiredCapabilityBinding
       then Some envelope.`oe_required_capability
       else None;
     ot_direct_predecessors = envelope.`oe_direct_predecessors;
     ot_authorization_digest = envelope.`oe_authorization_digest;
     ot_operation_kind = envelope.`oe_operation_kind;
     ot_operation_body =
       if defense_enabled mode DefenseOperationBodyBinding
       then Some envelope.`oe_operation_body
       else None;
     ot_nonce = envelope.`oe_nonce |}.

op production_transcript (envelope : operation_envelope) : operation_transcript =
  operation_transcript Production envelope.

op operation_signature_message
    (mode : validator_mode)
    (envelope : operation_envelope) : signature_message =
  OperationSignatureMessage (operation_transcript mode envelope).

op fact_signature_message (fact : authorization_fact) : signature_message =
  AuthorizationFactSignatureMessage fact.

op production_node_material
    (envelope : operation_envelope)
    (sig : signature) : node_material =
  {| nm_transcript = production_transcript envelope;
     nm_signature = sig |}.

lemma decode_encode_operation (envelope : operation_envelope) :
  decode_operation (encode_operation envelope) = Some envelope.
proof. by rewrite /decode_operation /encode_operation. qed.

lemma encode_operation_injective
    (left right : operation_envelope) :
  encode_operation left = encode_operation right => left = right.
proof. by rewrite /encode_operation; smt(). qed.

lemma encoded_operation_is_canonical (envelope : operation_envelope) :
  canonical_reencoding (encode_operation envelope).
proof. by rewrite /canonical_reencoding /encode_operation. qed.

lemma noncanonical_operation_is_rejected
    (envelope : operation_envelope) (bytes : raw_bytes) :
  ! canonical_reencoding (NonCanonicalWire envelope bytes).
proof. by rewrite /canonical_reencoding. qed.

lemma malformed_operation_does_not_decode (bytes : raw_bytes) :
  decode_operation (MalformedWire bytes) = None.
proof. by rewrite /decode_operation. qed.
