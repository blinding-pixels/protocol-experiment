require import AllCore List FSet.
require import ProtocolTypes CanonicalEncoding ProtocolPrimitives.
require import UnauthorizedSignatureReduction UnauthorizedOriginGame.

import PG.

(* A1 runs the same origin-aware A0 environment.  Only the node hash is wrapped
   so every production node-material query is retained by the primitive
   collision game. *)
module UnauthorizedOriginA1HashEvidence(
  A : ADAPTIVE_ORIGIN_UNAUTHORIZED_ADVERSARY,
  S : SIGNATURE_SCHEME,
  H : NODE_HASH
) = {
  module SO = PG.LoggedSignatureOracle(S)
  module HLog = PG.LoggedNodeHash(H)
  module O = OriginTrackedCandidateEnvironment(SO, HLog)
  module A = A(O)

  proc main(initial_state : protocol_state) : bool * bool = {
    var queries : PG.node_hash_query list;
    var found : PG.node_collision option;

    SO.init();
    HLog.init();
    O.init(initial_state);
    A.attack();
    queries <@ HLog.get_queries();
    found <- PG.find_node_collision_pair queries;

    return (O.unauthorized_accepted, found <> None);
  }
}.

module BHashOrigin(
  A : ADAPTIVE_ORIGIN_UNAUTHORIZED_ADVERSARY,
  S : SIGNATURE_SCHEME
)(O : PG.LOGGED_NODE_HASH_ORACLE) = {
  module SO = PG.LoggedSignatureOracle(S)
  module E = OriginTrackedCandidateEnvironment(SO, O)
  module A = A(E)

  proc collide(initial_state : protocol_state) : PG.node_collision = {
    var queries : PG.node_hash_query list;
    var found : PG.node_collision option;
    var pair : PG.node_collision;

    SO.init();
    E.init(initial_state);
    A.attack();
    queries <@ O.get_queries();
    found <- PG.find_node_collision_pair queries;
    pair <- if found = None then (witness, witness) else oget found;
    return pair;
  }
}.

section OriginA1ExactReduction.
  declare module A <: ADAPTIVE_ORIGIN_UNAUTHORIZED_ADVERSARY.
  declare module S <: SIGNATURE_SCHEME.
  declare module H <: NODE_HASH.

  lemma origin_bad_hash_exactly_reduces_to_node_collision
      &m initial_state :
    Pr[
      UnauthorizedOriginA1HashEvidence(A, S, H).main(initial_state) @ &m :
      res.`2
    ] =
    Pr[
      PG.NodeCollisionGame(BHashOrigin(A, S), H).main(initial_state) @ &m :
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
end section OriginA1ExactReduction.
