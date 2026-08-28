require import AllCore.
require import ProtocolTypes CanonicalEncoding.

(* Concrete cryptographic interfaces used by the executable protocol. Security
   claims about these interfaces live in PrimitiveGames.eca and the reduction
   files; the validator receives modules implementing the exact procedures. *)
module type SIGNATURE_SCHEME = {
  proc sign(
    vk : verification_key,
    message : signature_message
  ) : signature

  proc verify(
    vk : verification_key,
    message : signature_message,
    bytes : signature_bytes
  ) : bool
}.

module type NODE_HASH = {
  proc hash(material : node_material) : node_id
}.

module type TRANSCRIPT_HASH = {
  proc hash(transcript : operation_transcript) : node_id
}.

(* Deliberately insecure executable controls. They are used only by mutation
   witnesses and primitive-game sanity checks, never as a security premise. *)
module TestSignature : SIGNATURE_SCHEME = {
  proc sign(
    vk : verification_key,
    message : signature_message
  ) : signature = {
    return
      {| sig_verification_key = vk;
         sig_bytes = SignatureBytes message |};
  }

  proc verify(
    vk : verification_key,
    message : signature_message,
    bytes : signature_bytes
  ) : bool = {
    return bytes = SignatureBytes message;
  }
}.

module TestNodeHash : NODE_HASH = {
  proc hash(material : node_material) : node_id = {
    return NodeId 0;
  }
}.

module TestTranscriptHash : TRANSCRIPT_HASH = {
  proc hash(transcript : operation_transcript) : node_id = {
    return NodeId 0;
  }
}.
