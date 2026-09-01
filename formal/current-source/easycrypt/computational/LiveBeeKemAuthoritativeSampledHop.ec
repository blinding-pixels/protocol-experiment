require import AllCore List FSet Distr DBool.
require import ProtocolTypes ProtocolPrimitives.
require import LiveKeyGame LiveAuthenticationReduction.
require import LivePrfGame LivePrfAuthoritativeReduction.
require import BeeKemTypes BeeKemProtocol BeeKemSafety BeeKemKiGame.
require import BeeKemConstruction BeeKemProjectedNormalization.
require import LiveBeeKemAuthoritativeLiveTypes.
require import LiveBeeKemAuthoritativeAuthentication.
require import LiveBeeKemAuthoritativeSampledReduction.

(* Exact L1--L2 bridge for the sampled application experiment.  Both sides use
   the same production validator, canonical BeeKEM implementation, application
   oracle, KDF oracle, sampler, adversary, and call order.  The left side reads
   the complete application evidence directly; the right side packages the
   same application win bit as the concrete KI-DCGKA adversary's guess. *)
section AuthoritativeSampledRootProjection.
  declare module A <: AUTHORITATIVE_LIVE_KEY_ADVERSARY.
  declare module S <: SIGNATURE_SCHEME.
  declare module H <: NODE_HASH.
  declare module K <: MULTI_DOMAIN_KEY_SCHEDULE.
  declare module R <: LIVE_KEY_SAMPLER.
  declare module I <: BEEKEM_PAPER_INSTANCE.

  module L0 = AuthoritativeLiveRealGame(A, S, H, K, R, I).
  module Bee = AuthoritativeSampledLiveBeeKemGame(A, S, H, K, R, I).

  lemma authoritative_sampled_root_projection_exact
      &m (root_bit : bool) :
    Pr[
      L0.main_with_root_evidence(root_bit) @ &m :
        res.`alae_beekem_safe /\
        ! res.`alae_protocol_failure /\
        res.`alae_authenticated_win
    ] =
    Pr[
      Bee.main_with_fixed_bit(
        authoritative_live_initial_users,
        authoritative_live_initial_group,
        live_auth_retention_kappa,
        authoritative_live_initial_membership,
        root_bit
      ) @ &m :
        res.`bke_safe /\
        ! res.`bke_protocol_consistency_failure /\
        res.`bke_adversary_guess
    ].
  proof.
    byequiv
      (_ : ={root_bit, glob A, glob S, glob H, glob K, glob R, glob I}
           ==>
           (res{1}.`alae_beekem_safe /\
            ! res{1}.`alae_protocol_failure /\
            res{1}.`alae_authenticated_win) =
           (res{2}.`bke_safe /\
            ! res{2}.`bke_protocol_consistency_failure /\
            res{2}.`bke_adversary_guess)) => //.
    proc.
    inline L0.main_with_root_evidence L0.E.run.
    inline Bee.main_with_fixed_bit Bee.A.attack.
    sim.
  qed.
end section AuthoritativeSampledRootProjection.
