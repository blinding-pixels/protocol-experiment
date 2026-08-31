require import AllCore List FSet.
require import ProtocolTypes ProtocolPrimitives.
require import BeeKemTypes BeeKemKiGame BeeKemConstruction.
require import LiveKeyGame LivePrfTypes LivePrfGame.
require import LiveAuthenticationReduction.
require import LivePrfAuthoritativeReduction LivePrfAuthoritativeProof.
require import LiveBeeKemAuthoritativeLiveTypes.
require import LiveBeeKemAuthoritativeReduction.

(* Application one-event extracted from the canonical fixed-bit BeeKEM
   evidence.  The reduction adversary's guess already contains initial
   authorization validity, an actual accepted application challenge, absence
   of Deliverable-A authentication failure, absence of adapter fault, and the
   application adversary's guess.  The projection adds only the exact
   challenger-computed BeeKEM safety event and the explicit protocol-
   consistency boundary. *)
op authoritative_beekem_application_result
    (evidence : beekem_ki_evidence) : mdprf_adversary_result =
  {| mpar_eligible =
       evidence.`bke_safe /\
       ! evidence.`bke_protocol_consistency_failure;
     mpar_guess = evidence.`bke_adversary_guess |}.

lemma authoritative_beekem_application_result_event_exact
    (evidence : beekem_ki_evidence) :
  (authoritative_beekem_application_result evidence).`mpar_eligible /\
  (authoritative_beekem_application_result evidence).`mpar_guess =
    evidence.`bke_safe /\
    ! evidence.`bke_protocol_consistency_failure /\
    evidence.`bke_adversary_guess.
proof.
  by rewrite /authoritative_beekem_application_result.
qed.

lemma mdprf_fixed_bit_triangle (left middle right : real) :
  mdprf_fixed_bit_advantage left right <=
    mdprf_fixed_bit_advantage left middle +
    mdprf_fixed_bit_advantage middle right.
proof.
  rewrite /mdprf_fixed_bit_advantage.
  case (middle <= left); case (right <= middle); case (right <= left); smt().
qed.

section AuthoritativeBeeKemProjection.
  declare module A <: AUTHORITATIVE_LIVE_KEY_ADVERSARY.
  declare module S <: SIGNATURE_SCHEME.
  declare module H <: NODE_HASH.
  declare module K <: MULTI_DOMAIN_KEY_SCHEDULE.
  declare module R <: LIVE_KEY_SAMPLER.
  declare module I <: BEEKEM_PAPER_INSTANCE.

  module G = AuthoritativeLiveBeeKemGame(A, S, H, K, R, I).
  module Direct = AuthoritativePrfApplicationBit(A, S, H, K, R, I).
  module Prf = MultiDomainPrfGame(
    BPRFLiveAuthoritative(A, S, H, I), K, R
  ).

  module ProjectedRealRoot = {
    proc main() : mdprf_adversary_result = {
      var evidence : beekem_ki_evidence;

      evidence <@ G.main_with_fixed_bit(
        authoritative_live_initial_users,
        authoritative_live_initial_group,
        live_auth_retention_kappa,
        authoritative_live_initial_membership,
        true
      );
      return authoritative_beekem_application_result evidence;
    }
  }.

  module ProjectedRandomRoot = {
    proc main() : mdprf_adversary_result = {
      var evidence : beekem_ki_evidence;

      evidence <@ G.main_with_fixed_bit(
        authoritative_live_initial_users,
        authoritative_live_initial_group,
        live_auth_retention_kappa,
        authoritative_live_initial_membership,
        false
      );
      return authoritative_beekem_application_result evidence;
    }
  }.

  module PrfRealEndpoint = {
    proc main() : mdprf_adversary_result = {
      var result : mdprf_adversary_result;

      result <@ Direct.main(
        live_auth_initial_state,
        live_auth_initial_facts,
        live_auth_retention_kappa,
        true
      );
      return result;
    }
  }.

  module PrfRandomEndpoint = {
    proc main() : mdprf_adversary_result = {
      var result : mdprf_adversary_result;

      result <@ Direct.main(
        live_auth_initial_state,
        live_auth_initial_facts,
        live_auth_retention_kappa,
        false
      );
      return result;
    }
  }.

  lemma authoritative_prf_real_endpoint_exact
      &m :
    Pr[
      PrfRealEndpoint.main() @ &m :
        res.`mpar_eligible /\ res.`mpar_guess
    ] =
    Pr[
      Direct.main(
        live_auth_initial_state,
        live_auth_initial_facts,
        live_auth_retention_kappa,
        true
      ) @ &m :
        res.`mpar_eligible /\ res.`mpar_guess
    ].
  proof.
    byequiv
      (_ : ={glob A, glob S, glob H, glob K, glob R, glob I}
           ==>
           (res{1}.`mpar_eligible /\ res{1}.`mpar_guess) =
           (res{2}.`mpar_eligible /\ res{2}.`mpar_guess)) => //.
    proc.
    inline PrfRealEndpoint.main.
    sim.
  qed.

  lemma authoritative_prf_random_endpoint_exact
      &m :
    Pr[
      PrfRandomEndpoint.main() @ &m :
        res.`mpar_eligible /\ res.`mpar_guess
    ] =
    Pr[
      Direct.main(
        live_auth_initial_state,
        live_auth_initial_facts,
        live_auth_retention_kappa,
        false
      ) @ &m :
        res.`mpar_eligible /\ res.`mpar_guess
    ].
  proof.
    byequiv
      (_ : ={glob A, glob S, glob H, glob K, glob R, glob I}
           ==>
           (res{1}.`mpar_eligible /\ res{1}.`mpar_guess) =
           (res{2}.`mpar_eligible /\ res{2}.`mpar_guess)) => //.
    proc.
    inline PrfRandomEndpoint.main.
    sim.
  qed.

  lemma authoritative_prf_endpoint_advantage_exactly_game
      &m :
    mdprf_fixed_bit_advantage
      (Pr[
         PrfRealEndpoint.main() @ &m :
           res.`mpar_eligible /\ res.`mpar_guess
       ])
      (Pr[
         PrfRandomEndpoint.main() @ &m :
           res.`mpar_eligible /\ res.`mpar_guess
       ]) =
    mdprf_fixed_bit_advantage
      (Pr[
         Prf.main_with_fixed_bit(
           live_auth_initial_state,
           live_auth_initial_facts,
           live_auth_retention_kappa,
           true
         ) @ &m :
           res.`mpge_eligible /\ res.`mpge_guess
       ])
      (Pr[
         Prf.main_with_fixed_bit(
           live_auth_initial_state,
           live_auth_initial_facts,
           live_auth_retention_kappa,
           false
         ) @ &m :
           res.`mpge_eligible /\ res.`mpge_guess
       ]).
  proof.
    rewrite
      (authoritative_prf_real_endpoint_exact &m)
      (authoritative_prf_random_endpoint_exact &m).
    exact
      (authoritative_application_fixed_bit_advantage_exactly_prf
         A S H K R I &m
         live_auth_initial_state
         live_auth_initial_facts
         live_auth_retention_kappa).
  qed.

  lemma authoritative_beekem_real_projection_exact
      &m :
    Pr[
      ProjectedRealRoot.main() @ &m :
        res.`mpar_eligible /\ res.`mpar_guess
    ] =
    Pr[
      G.main_with_fixed_bit(
        authoritative_live_initial_users,
        authoritative_live_initial_group,
        live_auth_retention_kappa,
        authoritative_live_initial_membership,
        true
      ) @ &m :
        res.`bke_safe /\
        ! res.`bke_protocol_consistency_failure /\
        res.`bke_adversary_guess
    ].
  proof.
    byequiv (_ : ={glob A, glob S, glob H, glob K, glob R, glob I}
      ==> (res{1}.`mpar_eligible /\ res{1}.`mpar_guess) =
          (res{2}.`bke_safe /\
           ! res{2}.`bke_protocol_consistency_failure /\
           res{2}.`bke_adversary_guess)) => //.
    proc.
    call (_ : true).
    auto.
    by rewrite /authoritative_beekem_application_result.
  qed.

  lemma authoritative_beekem_random_projection_exact
      &m :
    Pr[
      ProjectedRandomRoot.main() @ &m :
        res.`mpar_eligible /\ res.`mpar_guess
    ] =
    Pr[
      G.main_with_fixed_bit(
        authoritative_live_initial_users,
        authoritative_live_initial_group,
        live_auth_retention_kappa,
        authoritative_live_initial_membership,
        false
      ) @ &m :
        res.`bke_safe /\
        ! res.`bke_protocol_consistency_failure /\
        res.`bke_adversary_guess
    ].
  proof.
    byequiv (_ : ={glob A, glob S, glob H, glob K, glob R, glob I}
      ==> (res{1}.`mpar_eligible /\ res{1}.`mpar_guess) =
          (res{2}.`bke_safe /\
           ! res{2}.`bke_protocol_consistency_failure /\
           res{2}.`bke_adversary_guess)) => //.
    proc.
    call (_ : true).
    auto.
    by rewrite /authoritative_beekem_application_result.
  qed.

  (* H1 is the canonical BeeKEM random-root branch with the actual
     multi-domain PRF oracle fixed to its real branch.  The right-hand endpoint
     is the same production application execution exposed directly by the PRF
     reduction.  Only the two enclosing game wrappers are unfolded here. *)
  lemma authoritative_beekem_random_root_exactly_prf_real
      &m :
    Pr[
      ProjectedRandomRoot.main() @ &m :
        res.`mpar_eligible /\ res.`mpar_guess
    ] =
    Pr[
      PrfRealEndpoint.main() @ &m :
        res.`mpar_eligible /\ res.`mpar_guess
    ].
  proof.
    byequiv
      (_ : ={glob A, glob S, glob H, glob K, glob R, glob I}
           ==>
           (res{1}.`mpar_eligible /\ res{1}.`mpar_guess) =
           (res{2}.`mpar_eligible /\ res{2}.`mpar_guess)) => //.
    proc.
    inline ProjectedRandomRoot.main PrfRealEndpoint.main.
    inline G.main_with_fixed_bit G.A.attack Direct.main.
    sim.
  qed.

  (* The executable L0--L3 distance is split at the checker-proved shared H1
     endpoint.  This is ordinary absolute-distance triangle algebra after both
     program equalities above; it introduces no assumed adjacent-game hop. *)
  lemma authoritative_live_hybrid_triangle &m :
    mdprf_fixed_bit_advantage
      (Pr[
         ProjectedRealRoot.main() @ &m :
           res.`mpar_eligible /\ res.`mpar_guess
       ])
      (Pr[
         PrfRandomEndpoint.main() @ &m :
           res.`mpar_eligible /\ res.`mpar_guess
       ])
    <=
    mdprf_fixed_bit_advantage
      (Pr[
         ProjectedRealRoot.main() @ &m :
           res.`mpar_eligible /\ res.`mpar_guess
       ])
      (Pr[
         ProjectedRandomRoot.main() @ &m :
           res.`mpar_eligible /\ res.`mpar_guess
       ])
    +
    mdprf_fixed_bit_advantage
      (Pr[
         PrfRealEndpoint.main() @ &m :
           res.`mpar_eligible /\ res.`mpar_guess
       ])
      (Pr[
         PrfRandomEndpoint.main() @ &m :
           res.`mpar_eligible /\ res.`mpar_guess
       ]).
  proof.
    rewrite -authoritative_beekem_random_root_exactly_prf_real.
    exact (mdprf_fixed_bit_triangle
      (Pr[
         ProjectedRealRoot.main() @ &m :
           res.`mpar_eligible /\ res.`mpar_guess
       ])
      (Pr[
         ProjectedRandomRoot.main() @ &m :
           res.`mpar_eligible /\ res.`mpar_guess
       ])
      (Pr[
         PrfRandomEndpoint.main() @ &m :
           res.`mpar_eligible /\ res.`mpar_guess
       ])).
  qed.

  lemma authoritative_live_hybrid_triangle_prf_game &m :
    mdprf_fixed_bit_advantage
      (Pr[
         ProjectedRealRoot.main() @ &m :
           res.`mpar_eligible /\ res.`mpar_guess
       ])
      (Pr[
         PrfRandomEndpoint.main() @ &m :
           res.`mpar_eligible /\ res.`mpar_guess
       ])
    <=
    mdprf_fixed_bit_advantage
      (Pr[
         ProjectedRealRoot.main() @ &m :
           res.`mpar_eligible /\ res.`mpar_guess
       ])
      (Pr[
         ProjectedRandomRoot.main() @ &m :
           res.`mpar_eligible /\ res.`mpar_guess
       ])
    +
    mdprf_fixed_bit_advantage
      (Pr[
         Prf.main_with_fixed_bit(
           live_auth_initial_state,
           live_auth_initial_facts,
           live_auth_retention_kappa,
           true
         ) @ &m :
           res.`mpge_eligible /\ res.`mpge_guess
       ])
      (Pr[
         Prf.main_with_fixed_bit(
           live_auth_initial_state,
           live_auth_initial_facts,
           live_auth_retention_kappa,
           false
         ) @ &m :
           res.`mpge_eligible /\ res.`mpge_guess
       ]).
  proof.
    rewrite -(authoritative_prf_endpoint_advantage_exactly_game &m).
    exact (authoritative_live_hybrid_triangle &m).
  qed.
end section AuthoritativeBeeKemProjection.
