require import AllCore List FSet Distr DBool.
require import ProtocolTypes ProtocolPrimitives.
require import LiveKeyGame LivePrfGame.
require import LiveAuthenticationReduction.
require import BeeKemConstruction.
require import LiveBeeKemAuthoritativeLiveTypes.
require import LiveBeeKemAuthoritativeAuthentication.

(* Public L0 entry points are projections of one shared evidence-producing
   execution.  These equalities keep the final theorem attached to the actual
   [main] procedure while allowing the reduction chain to reason about the
   challenger-owned root bit and the complete evidence record. *)
section AuthoritativeLiveEntryBridge.
  declare module A <: AUTHORITATIVE_LIVE_KEY_ADVERSARY.
  declare module S <: SIGNATURE_SCHEME.
  declare module H <: NODE_HASH.
  declare module K <: MULTI_DOMAIN_KEY_SCHEDULE.
  declare module R <: LIVE_KEY_SAMPLER.
  declare module I <: BEEKEM_PAPER_INSTANCE.

  module L0 = AuthoritativeLiveRealGame(A, S, H, K, R, I).

  lemma authoritative_live_evidence_authenticated_exactly_real_root
      &m :
    Pr[
      L0.main_with_evidence() @ &m : res.`alae_authenticated_win
    ] =
    Pr[
      L0.main_with_root_evidence(true) @ &m :
        res.`alae_authenticated_win
    ].
  proof.
    byequiv
      (_ : ={glob A, glob S, glob H, glob K, glob R, glob I}
           ==>
           res{1}.`alae_authenticated_win =
           res{2}.`alae_authenticated_win) => //.
    proc.
    inline L0.main_with_root_evidence
      L0.main_with_root_and_application_bit.
    sim.
  qed.

  lemma authoritative_live_public_raw_exactly_evidence
      &m :
    Pr[L0.main() @ &m : res] =
    Pr[L0.main_with_evidence() @ &m : res.`alae_raw_win].
  proof.
    byequiv
      (_ : ={glob A, glob S, glob H, glob K, glob R, glob I}
           ==> res{1} = res{2}.`alae_raw_win) => //.
    proc.
    call (_ : true).
    auto.
  qed.

  lemma authoritative_live_public_authenticated_exactly_evidence
      &m :
    Pr[L0.authenticated_main() @ &m : res] =
    Pr[
      L0.main_with_evidence() @ &m : res.`alae_authenticated_win
    ].
  proof.
    byequiv
      (_ : ={glob A, glob S, glob H, glob K, glob R, glob I}
           ==> res{1} = res{2}.`alae_authenticated_win) => //.
    proc.
    call (_ : true).
    auto.
  qed.
end section AuthoritativeLiveEntryBridge.
