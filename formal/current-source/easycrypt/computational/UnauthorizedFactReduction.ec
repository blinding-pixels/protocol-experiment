require import AllCore List FSet.
require import ProtocolTypes CanonicalEncoding ProtocolPrimitives AuthorizationState.
require PrimitiveGames.
clone import PrimitiveGames as PG.
require import UnauthorizedSignatureReduction UnauthorizedReduction.

(* Convert the signed authorization facts supplied in an accepted public view
   into the exact primitive-message candidates checked by the shared
   normalizer. *)
op fact_signature_candidates
    (facts : signed_authorization_fact list) : PG.signature_forgery list =
  with facts = [] => []
  with facts = signed_fact :: rest =>
    {| sf_verification_key =
         signed_fact.`saf_signature.`sig_verification_key;
       sf_message = fact_signature_message signed_fact.`saf_fact;
       sf_signature = signed_fact.`saf_signature |}
      :: fact_signature_candidates rest.

op find_fact_signature_forgery
    (accepted : PG.signature_forgery list)
    (sign_queries : PG.signature_query list)
    (verify_queries : PG.signature_verification_query list) :
    PG.signature_forgery option =
  with accepted = [] => None
  with accepted = candidate :: rest =>
    if PG.signature_forgery_valid candidate sign_queries verify_queries
    then Some candidate
    else find_fact_signature_forgery rest sign_queries verify_queries.

module CandidateFactSignatureEnvironment(
  SO : PG.LOGGED_SIGNATURE_ORACLE,
  H : NODE_HASH
) = {
  module Base = CandidateSignatureEnvironment(SO, H)

  var accepted_fact_signatures : PG.signature_forgery list
  var unauthorized_accepted : bool

  proc init(initial_state : protocol_state) : unit = {
    Base.init(initial_state);
    accepted_fact_signatures <- [];
    unauthorized_accepted <- false;
  }

  proc sign(
    vk : verification_key,
    message : signature_message
  ) : signature = {
    var sig : signature;
    sig <@ Base.sign(vk, message);
    return sig;
  }

  proc submit(
    operation : signed_operation,
    view : public_view
  ) : bool = {
    var accepted : bool;

    accepted <@ Base.submit(operation, view);
    if (accepted) {
      accepted_fact_signatures <-
        accepted_fact_signatures ++ fact_signature_candidates view.`pv_facts;
    }
    unauthorized_accepted <- Base.unauthorized_accepted;
    return accepted;
  }
}.

module UnauthorizedA3FactEvidence(
  A : ADAPTIVE_SIGNED_UNAUTHORIZED_ADVERSARY,
  S : SIGNATURE_SCHEME,
  H : NODE_HASH
) = {
  module SO = PG.LoggedSignatureOracle(S)
  module O = CandidateFactSignatureEnvironment(SO, H)
  module A = A(O)

  proc main(initial_state : protocol_state) : bool * bool = {
    var sign_queries : PG.signature_query list;
    var verify_queries : PG.signature_verification_query list;
    var forgery : PG.signature_forgery option;

    SO.init();
    O.init(initial_state);
    A.attack();
    sign_queries <@ SO.get_sign_queries();
    verify_queries <@ SO.get_verify_queries();
    forgery <- find_fact_signature_forgery
      O.accepted_fact_signatures sign_queries verify_queries;

    return (O.unauthorized_accepted, forgery <> None);
  }
}.

module BSignFacts(
  A : ADAPTIVE_SIGNED_UNAUTHORIZED_ADVERSARY,
  H : NODE_HASH
)(SO : PG.LOGGED_SIGNATURE_ORACLE) = {
  module O = CandidateFactSignatureEnvironment(SO, H)
  module A = A(O)

  proc forge(initial_state : protocol_state) : PG.signature_forgery option = {
    var sign_queries : PG.signature_query list;
    var verify_queries : PG.signature_verification_query list;
    var forgery : PG.signature_forgery option;

    O.init(initial_state);
    A.attack();
    sign_queries <@ SO.get_sign_queries();
    verify_queries <@ SO.get_verify_queries();
    forgery <- find_fact_signature_forgery
      O.accepted_fact_signatures sign_queries verify_queries;
    return forgery;
  }
}.

section A3FactSignatureReduction.
  declare module A <: ADAPTIVE_SIGNED_UNAUTHORIZED_ADVERSARY.
  declare module S <: SIGNATURE_SCHEME.
  declare module H <: NODE_HASH.

  lemma bad_fact_signature_exactly_reduces_to_multi_user_eufcma
      &m initial_state :
    Pr[
      UnauthorizedA3FactEvidence(A, S, H).main(initial_state) @ &m :
      res.`2
    ] =
    Pr[
      PG.MultiUserEUFCMAGame(BSignFacts(A, H), S).main(initial_state) @ &m :
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
end section A3FactSignatureReduction.

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

  lemma normalize_success_implies_policy_ancestry :
    hoare [NormalizeAuthorization(S).normalize :
      true ==>
      res.`1 => authorization_ancestry_valid creator facts res.`2].
  proof.
    proc.
    while
      (valid =>
        authorization_policy_replay_from
          current snapshots creator remaining =
        authorization_policy_replay creator facts).
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
