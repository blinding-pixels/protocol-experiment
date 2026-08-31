require import AllCore List FSet Distr DBool.
require import ProtocolTypes CanonicalEncoding ProtocolPrimitives AuthorizationState UnauthorizedSignatureReduction.
require import UnauthorizedOriginGame LiveKeyGame LiveAuthenticationReduction.
require import LiveBeeKemOracle.
require LiveBeeKemKiInterface.
clone import LiveBeeKemKiInterface as BKI.

import PG.

(* Concrete L2 reduction adversary.  Its output is the authenticated application
   experiment's success indicator.  In the primitive real-root world this is
   the L1 application experiment; in the random-root world it is the next
   hybrid.  No protocol security conclusion is assumed here. *)
module BBeeLive(
  A : LIVE_KEY_ADVERSARY,
  S : SIGNATURE_SCHEME,
  H : NODE_HASH,
  K : MULTI_DOMAIN_KEY_SCHEDULE,
  R : LIVE_KEY_SAMPLER
)(O : BKI.BEEKEM_KI_ORACLE) = {
  module SO = PG.LoggedSignatureOracle(S)
  module Auth = OriginTrackedCandidateEnvironment(SO, H)
  module Live = KiBackedLiveOracle(Auth, O, K, R)
  module A = A(Live)

  proc attack() : bool = {
    var application_bit : bool;
    var adversary_guess : bool;

    SO.init();
    Auth.init(live_auth_initial_state);
    application_bit <$ {0,1};
    Live.init(
      live_auth_initial_state,
      live_auth_retention_kappa,
      application_bit,
      live_auth_initial_digest
    );
    A.attack();
    adversary_guess <@ A.guess();

    return
         live_auth_initial_authorization <> None
      /\ live_trace_admissible
           live_auth_retention_kappa
           Live.D.Base.Core.relation Live.D.queries
           (Live.D.Base.Core.runtime_fault \/ Live.D.Base.runtime_fault)
      /\ ! Auth.unauthorized_accepted
      /\ adversary_guess = application_bit;
  }
}.

(* Checker-backed connectivity control: two derived outputs at one root invoke
   the primitive Challenge oracle once and reuse its exact response. *)
module CountingBeeKemKiOracle : BKI.BEEKEM_KI_ORACLE = {
  module B = TestBeeKemLiveRuntime

  var challenge_calls : int

  proc init() : unit = {
    B.init();
    challenge_calls <- 0;
  }

  proc create_group(
    creator : principal,
    initial_members : principal fset,
    digest : authorization_digest
  ) : beekem_step_result = {
    var result : beekem_step_result;
    result <@ B.create_group(creator, initial_members, digest);
    return result;
  }

  proc add_member(
    author : principal,
    target : principal,
    digest : authorization_digest
  ) : beekem_step_result = {
    var result : beekem_step_result;
    result <@ B.add_member(author, target, digest);
    return result;
  }

  proc remove_member(
    author : principal,
    target : principal,
    digest : authorization_digest
  ) : beekem_step_result = {
    var result : beekem_step_result;
    result <@ B.remove_member(author, target, digest);
    return result;
  }

  proc send_update(
    author : principal,
    digest : authorization_digest
  ) : beekem_step_result = {
    var result : beekem_step_result;
    result <@ B.send_update(author, digest);
    return result;
  }

  proc deliver(
    message : beekem_control_message,
    recipient : principal
  ) : beekem_secret option = {
    var result : beekem_secret option;
    result <@ B.deliver(message, recipient);
    return result;
  }

  proc reveal(
    member : principal,
    node : node_id
  ) : beekem_secret option = {
    return Some (test_secret_for_node node);
  }

  proc challenge(
    member : principal,
    node : node_id
  ) : beekem_secret option = {
    challenge_calls <- challenge_calls + 1;
    return Some (test_secret_for_node node);
  }

  proc compromise(member : principal) : beekem_snapshot = {
    var result : beekem_snapshot;
    result <@ B.compromise(member);
    return result;
  }
}.

op wrapper_control_creator : principal =
  {| p_verification_key = VerificationKey 810;
     p_incarnation_nonce = IncarnationNonce 811 |}.

op wrapper_control_state : protocol_state =
  {| ps_creator = wrapper_control_creator;
     ps_document_id = DocumentId 812;
     ps_nodes = fset0;
     ps_closures = fun _ => None;
     ps_fact_contents = fun _ => None;
     ps_seen_operation_ids = fset0;
     ps_seen_nonces = fset0;
     ps_beekem_paths = fun _ => None;
     ps_history_expectation = None;
     ps_expected_puncture_regions = fset0 |}.

module WrapperAuth : ORIGIN_TRACKED_UNAUTHORIZED_ORACLE = {
  proc sign_operation(
    envelope : operation_envelope
  ) : signed_operation = {
    return witness;
  }

  proc sign_authorization_fact(
    fact : authorization_fact
  ) : signed_authorization_fact = {
    return witness;
  }

  proc submit(
    operation : signed_operation,
    view : public_view
  ) : bool = {
    return false;
  }
}.

module BeeKemWrapperChallengeControl = {
  module O = KiBackedLiveOracle(
    WrapperAuth,
    CountingBeeKemKiOracle,
    TestMultiDomainKeySchedule,
    TestLiveKeySampler
  )

  proc main() : bool * int = {
    var created : node_id option;
    var updated : node_id option;
    var history : history_domain_output option;
    var challenge : live_application_key option;

    CountingBeeKemKiOracle.init();
    O.init(
      wrapper_control_state,
      1,
      true,
      authorization_digest_of empty_authorization_state
    );
    created <@ O.create_group(wrapper_control_creator, fset0);
    updated <@ O.send_beekem_update(wrapper_control_creator);
    history <@ O.reveal_history_output(
      wrapper_control_creator, NodeId 2, SegmentId 813
    );
    challenge <@ O.challenge_live(wrapper_control_creator, NodeId 2);

    return
      (history <> None /\ challenge <> None,
       CountingBeeKemKiOracle.challenge_calls);
  }
}.

lemma beekem_live_wrapper_invokes_primitive_challenge_once :
  hoare [BeeKemWrapperChallengeControl.main :
    true ==> res = (true, 1)].
proof.
  proc.
  inline *.
  auto.
  rewrite /wrapper_control_state /wrapper_control_creator
    /empty_beekem_root_cache /beekem_root_cache_put
    /empty_active_member_store /active_member_store_put
    /active_member_store_of_set
    /empty_control_store /empty_node_digest_store
    /empty_delivery_store /empty_member_secret_store
    /empty_member_head_store /empty_causal_relation
    /control_store_put /node_digest_store_put
    /delivery_store_put /member_secret_store_put
    /member_head_store_put /node_after /test_secret_for_node
    /history_label_of /live_label_of
    /test_history_material /test_live_material
    /all_nodes_known /all_nodes_known_list
    /all_predecessors_delivered /all_predecessors_delivered_list
    /causal_relation_extend /predecessor_reaches_list /=.
  by rewrite !inE; smt().
qed.
