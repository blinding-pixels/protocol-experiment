require import AllCore List FSet.
require import ProtocolTypes CanonicalEncoding ProtocolPrimitives PrimitiveGames.
require import UnauthorizedReduction.

(* EasyCrypt-level canonical encoding is injective by construction.  This is
   deterministic representation reasoning, not a collision-resistance
   assumption. *)
lemma canonical_encoding_failure_impossible
    (left right : operation_envelope) :
  left <> right => encode_operation left <> encode_operation right.
proof.
  by move=> neq equal; apply neq; exact (encode_operation_injective left right equal).
qed.

(* Instrument A0 with the node-hash oracle from the exact primitive collision
   game.  The protocol environment still calls the shared production
   validator; only the hash implementation is wrapped to retain its actual
   input/output query log. *)
module UnauthorizedA1HashEvidence(
  A : ADAPTIVE_UNAUTHORIZED_ADVERSARY,
  S : SIGNATURE_SCHEME,
  H : NODE_HASH
) = {
  module HLog = LoggedNodeHash(H)
  module O = CandidateUnauthorizedEnvironment(S, HLog)
  module A = A(O)

  proc main(initial_state : protocol_state) : bool * bool = {
    var queries : node_hash_query list;
    var found : node_collision option;

    HLog.init();
    O.init(initial_state);
    A.attack();
    queries <@ HLog.get_queries();
    found <- find_node_collision_pair queries;

    return (O.unauthorized_accepted, found <> None);
  }
}.

(* Named A1 reduction.  It runs the adaptive unauthorized adversary through
   the same validator environment, obtains the actual node-hash query log from
   its primitive oracle, and outputs the concrete colliding pair found there.
   When no collision occurred it returns a dummy equal pair, which cannot win
   [NodeCollisionGame]. *)
module BHash(
  A : ADAPTIVE_UNAUTHORIZED_ADVERSARY,
  S : SIGNATURE_SCHEME
)(O : LOGGED_NODE_HASH_ORACLE) = {
  module E = CandidateUnauthorizedEnvironment(S, O)
  module A = A(E)

  proc collide(initial_state : protocol_state) : node_collision = {
    var queries : node_hash_query list;
    var found : node_collision option;
    var pair : node_collision;

    E.init(initial_state);
    A.attack();
    queries <@ O.get_queries();
    found <- find_node_collision_pair queries;
    pair <- if found = None then (witness, witness) else oget found;
    return pair;
  }
}.

section A1ExactReduction.
  declare module A <: ADAPTIVE_UNAUTHORIZED_ADVERSARY.
  declare module S <: SIGNATURE_SCHEME.
  declare module H <: NODE_HASH.

  lemma bad_hash_exactly_reduces_to_node_collision &m initial_state :
    Pr[
      UnauthorizedA1HashEvidence(A, S, H).main(initial_state) @ &m :
      res.`2
    ] =
    Pr[
      NodeCollisionGame(BHash(A, S), H).main(initial_state) @ &m :
      res
    ].
  proof.
    byequiv
      (_ : ={initial_state, glob A, glob S, glob H} ==>
           res{1}.`2 = res{2}) => //.
    proc.
    inline *.
    sim.
  qed.
end section A1ExactReduction.
