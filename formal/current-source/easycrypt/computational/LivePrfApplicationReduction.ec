require import AllCore List FSet.
require import ProtocolTypes CanonicalEncoding ProtocolPrimitives AuthorizationState.
require import AuthorizationAncestry UnauthorizedSignatureReduction UnauthorizedOriginGame.
require import LiveKeyGame LivePrfTypes LivePrfGame.

import PG.

(* The application core exposes live reveals and live challenges through two
   different procedures, but its internal key-schedule call has one
   [derive_live] entry point.  This switch is controlled only by the wrapper
   immediately around [challenge_live]; the adversary cannot set it. *)
module type PRF_ORACLE_BACKED_KEY_SCHEDULE = {
  proc init() : unit
  proc begin_challenge() : unit
  proc end_challenge() : unit

  proc derive_live(
    secret : beekem_secret,
    label : live_key_label
  ) : live_application_key

  proc derive_history(
    secret : beekem_secret,
    label : history_key_label
  ) : history_domain_output

  proc derive_history_capability(
    secret : beekem_secret,
    label : history_key_label,
    cover : segment_cover
  ) : history_capability_output
}.

(* Application key-schedule adapter used by the concrete BPRFLive reduction.
   Ordinary live derivations are real-only and simulate application reveals.
   Only the derivation reached while the wrapper is executing an application
   challenge invokes the primitive challenge procedure.  History and
   constrained-history calls are forwarded to their real-domain procedures. *)
module PrfOracleBackedKeySchedule(
  O : MULTI_DOMAIN_PRF_ORACLE
) : PRF_ORACLE_BACKED_KEY_SCHEDULE = {
  var challenge_mode : bool

  proc init() : unit = {
    challenge_mode <- false;
  }

  proc begin_challenge() : unit = {
    challenge_mode <- true;
  }

  proc end_challenge() : unit = {
    challenge_mode <- false;
  }

  proc derive_live(
    secret : beekem_secret,
    label : live_key_label
  ) : live_application_key = {
    var answer : live_application_key;

    answer <- witness;
    if (challenge_mode) {
      answer <@ O.challenge_live(secret, label);
    } else {
      answer <@ O.derive_live(secret, label);
    }
    return answer;
  }

  proc derive_history(
    secret : beekem_secret,
    label : history_key_label
  ) : history_domain_output = {
    var answer : history_domain_output;
    answer <@ O.derive_history(secret, label);
    return answer;
  }

  proc derive_history_capability(
    secret : beekem_secret,
    label : history_key_label,
    cover : segment_cover
  ) : history_capability_output = {
    var answer : history_capability_output;
    answer <@ O.derive_history_capability(secret, label, cover);
    return answer;
  }
}.

(* Transparent application-oracle wrapper.  It forwards every procedure
   unchanged except [challenge_live], around which it opens and closes the
   challenger-owned switch.  Failed application challenges still close the
   switch and make no primitive challenge call. *)
module PrfBackedLiveOracle(
  Core : LIVE_PROTOCOL_ORACLE,
  K : PRF_ORACLE_BACKED_KEY_SCHEDULE
) : LIVE_PROTOCOL_ORACLE = {
  proc sign_operation(
    envelope : operation_envelope
  ) : signed_operation = {
    var result : signed_operation;
    result <@ Core.sign_operation(envelope);
    return result;
  }

  proc sign_authorization_fact(
    fact : authorization_fact
  ) : signed_authorization_fact = {
    var result : signed_authorization_fact;
    result <@ Core.sign_authorization_fact(fact);
    return result;
  }

  proc create_group(
    creator : principal,
    initial_members : principal fset
  ) : node_id option = {
    var result : node_id option;
    result <@ Core.create_group(creator, initial_members);
    return result;
  }

  proc add_member(
    author : principal,
    target : principal
  ) : node_id option = {
    var result : node_id option;
    result <@ Core.add_member(author, target);
    return result;
  }

  proc remove_member(
    author : principal,
    target : principal
  ) : node_id option = {
    var result : node_id option;
    result <@ Core.remove_member(author, target);
    return result;
  }

  proc send_beekem_update(
    author : principal
  ) : node_id option = {
    var result : node_id option;
    result <@ Core.send_beekem_update(author);
    return result;
  }

  proc deliver(
    node : node_id,
    recipient : principal
  ) : bool = {
    var result : bool;
    result <@ Core.deliver(node, recipient);
    return result;
  }

  proc reveal_live_key(
    member : principal,
    node : node_id
  ) : live_application_key option = {
    var result : live_application_key option;
    result <@ Core.reveal_live_key(member, node);
    return result;
  }

  proc challenge_live(
    member : principal,
    node : node_id
  ) : live_application_key option = {
    var result : live_application_key option;

    K.begin_challenge();
    result <@ Core.challenge_live(member, node);
    K.end_challenge();
    return result;
  }

  proc reveal_history_output(
    member : principal,
    node : node_id,
    segment : segment_id
  ) : history_domain_output option = {
    var result : history_domain_output option;
    result <@ Core.reveal_history_output(member, node, segment);
    return result;
  }

  proc reveal_history_capability(
    member : principal,
    node : node_id,
    segment : segment_id,
    cover : segment_cover
  ) : history_capability_output option = {
    var result : history_capability_output option;
    result <@ Core.reveal_history_capability(member, node, segment, cover);
    return result;
  }

  proc compromise_protocol_state(
    member : principal
  ) : beekem_snapshot option = {
    var result : beekem_snapshot option;
    result <@ Core.compromise_protocol_state(member);
    return result;
  }

  proc submit_operation(
    operation : signed_operation,
    view : public_view
  ) : bool = {
    var result : bool;
    result <@ Core.submit_operation(operation, view);
    return result;
  }
}.

(* LiveProtocolCore evaluates both key branches before selecting its application
   bit.  BPRFLive fixes that selector to the real branch, so this deterministic
   value is evaluated but never returned to the application adversary. *)
module PrfReductionUnusedSampler : LIVE_KEY_SAMPLER = {
  proc sample(label : live_key_label) : live_application_key = {
    return LiveApplicationKey 0 label;
  }
}.

(* Concrete application-to-primitive reduction.  [B] is deliberately the
   application BeeKEM runtime seam.  The current admissibility computation is
   provisional and must later be discharged against the authoritative complete
   BeeKEM query log; it is neither supplied by the adversary nor represented by
   a generic Boolean. *)
module BPRFLive(
  A : LIVE_KEY_ADVERSARY,
  S : SIGNATURE_SCHEME,
  H : NODE_HASH,
  B : BEEKEM_LIVE_RUNTIME
)(O : MULTI_DOMAIN_PRF_ORACLE) = {
  module SO = PG.LoggedSignatureOracle(S)
  module Auth = OriginTrackedCandidateEnvironment(SO, H)
  module K = PrfOracleBackedKeySchedule(O)
  module Core = LiveProtocolCore(Auth, B, K, PrfReductionUnusedSampler)
  module Live = PrfBackedLiveOracle(Core, K)
  module A = A(Live)

  proc attack(
    initial_state : protocol_state,
    initial_facts : signed_authorization_fact list,
    retention_kappa : int
  ) : mdprf_adversary_result = {
    var initial_authorization : authorization_state option;
    var initial_digest : authorization_digest;
    var adversary_guess : bool;
    var eligible : bool;

    initial_authorization <-
      live_initial_authorization initial_state initial_facts;
    initial_digest <-
      live_initial_authorization_digest initial_state initial_facts;
    adversary_guess <- false;
    eligible <- false;

    SO.init();
    Auth.init(initial_state);
    K.init();
    Core.init(initial_state, retention_kappa, true, initial_digest);
    A.attack();
    adversary_guess <@ A.guess();

    eligible <-
         initial_authorization <> None
      /\ live_trace_admissible
           retention_kappa Core.relation Core.queries Core.runtime_fault
      /\ ! Auth.unauthorized_accepted;

    return
      {| mpar_eligible = eligible;
         mpar_guess = adversary_guess |};
  }
}.
