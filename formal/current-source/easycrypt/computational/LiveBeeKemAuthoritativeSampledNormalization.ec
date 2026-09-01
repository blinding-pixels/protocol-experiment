require import AllCore List FSet Distr DBool.
require import ProtocolTypes ProtocolPrimitives.
require import LiveKeyGame LivePrfGame.
require import BeeKemConstruction.
require import LiveBeeKemAuthoritativeLiveTypes.
require import LiveBeeKemAuthoritativeAuthentication.
require import LiveBeeKemAuthoritativeAuthenticationBound.
require import LiveBeeKemAuthoritativeSampledHop.

(* Ordinary hidden-bit success for a decision bit that is forced to false when
   the executable admissibility filter rejects.  Under a lossless fixed-bit
   execution this is exactly the fixed-bit one-event distance divided by two. *)
op authoritative_standard_hidden_bit_success
    (real_one_probability random_one_probability : real) : real =
  (real_one_probability + (1%r - random_one_probability)) / 2%r.

lemma authoritative_standard_hidden_bit_normalization
    (real_one_probability random_one_probability : real) :
  authoritative_live_normalized_advantage
    (authoritative_standard_hidden_bit_success
       real_one_probability random_one_probability) =
  mdprf_fixed_bit_advantage
    real_one_probability random_one_probability / 2%r.
proof.
  rewrite /authoritative_standard_hidden_bit_success
    /authoritative_live_normalized_advantage
    /mdprf_normalized_advantage
    /mdprf_fixed_bit_advantage.
  case (random_one_probability <= real_one_probability); smt().
qed.

section AuthoritativeSampledApplicationNormalization.
  declare module A <: AUTHORITATIVE_LIVE_KEY_ADVERSARY.
  declare module S <: SIGNATURE_SCHEME.
  declare module H <: NODE_HASH.
  declare module K <: MULTI_DOMAIN_KEY_SCHEDULE.
  declare module R <: LIVE_KEY_SAMPLER.
  declare module I <: BEEKEM_PAPER_INSTANCE.

  module G = AuthoritativeLiveRealGame(A, S, H, K, R, I).

  module FairApplicationBitRunner = {
    var sampled_bit : bool

    proc main(root_bit : bool) : bool = {
      var evidence : authoritative_live_application_evidence;

      sampled_bit <$ dbool;
      if (sampled_bit) {
        evidence <@ G.main_with_root_and_application_bit(
          root_bit, true
        );
      } else {
        evidence <@ G.main_with_root_and_application_bit(
          root_bit, false
        );
      }
      return evidence.`alae_authenticated_win;
    }
  }.

  lemma authoritative_sampled_root_equiv_fair_application_runner
      &m (root_bit : bool) :
    Pr[
      G.main_with_root_evidence(root_bit) @ &m :
        res.`alae_authenticated_win
    ] =
    Pr[
      FairApplicationBitRunner.main(root_bit) @ &m : res
    ].
  proof.
    byequiv
      (_ : ={root_bit, glob A, glob S, glob H,
             glob K, glob R, glob I}
           ==> res{1}.`alae_authenticated_win = res{2}) => //.
    proc.
    inline G.main_with_root_evidence.
    rnd.
    if{2}; call (_ : true); auto.
  qed.

  lemma authoritative_sampled_root_win_probability_is_fixed_bit_average
      &m (root_bit : bool) :
    Pr[
      G.main_with_root_evidence(root_bit) @ &m :
        res.`alae_authenticated_win
    ] =
      (Pr[
         G.main_with_root_and_application_bit(
           root_bit, true
         ) @ &m : res.`alae_authenticated_win
       ] +
       Pr[
         G.main_with_root_and_application_bit(
           root_bit, false
         ) @ &m : res.`alae_authenticated_win
       ]) / 2%r.
  proof.
    rewrite authoritative_sampled_root_equiv_fair_application_runner.
    have -> :
      Pr[
        FairApplicationBitRunner.main(root_bit) @ &m : res
      ] =
      Pr[
        FairApplicationBitRunner.main(root_bit) @ &m :
          res /\ FairApplicationBitRunner.sampled_bit
      ] +
      Pr[
        FairApplicationBitRunner.main(root_bit) @ &m :
          res /\ ! FairApplicationBitRunner.sampled_bit
      ].
    + by rewrite Pr[mu_split FairApplicationBitRunner.sampled_bit].

    have Htrue :
      Pr[
        FairApplicationBitRunner.main(root_bit) @ &m :
          res /\ FairApplicationBitRunner.sampled_bit
      ] =
      1%r / 2%r *
      Pr[
        G.main_with_root_and_application_bit(
          root_bit, true
        ) @ &m : res.`alae_authenticated_win
      ].
    + byphoare (_ :
          (glob G) = (glob G){m} /\ arg = root_bit
       ==>
          res /\ FairApplicationBitRunner.sampled_bit) => //.
      proc.
      pose p := Pr[
        G.main_with_root_and_application_bit(
          root_bit, true
        ) @ &m : res.`alae_authenticated_win
      ].
      seq 1 :
        (FairApplicationBitRunner.sampled_bit = true /\
         root_bit{hr} = root_bit)
        (1%r / 2%r) p _ 0%r
        ((glob G) = (glob G){m} /\ root_bit{hr} = root_bit);
        first by auto.
      + by rnd (pred1 true); skip => />; rewrite dbool1E.
      + if; last by (conseq (_ : false ==> _); 1:by smt()); auto.
        conseq (_ : _ ==> evidence.`alae_authenticated_win) => //;
          first by smt().
        call (_ :
          arg = (root_bit, true) /\ (glob G) = (glob G){m}
          ==> res.`alae_authenticated_win); last by auto.
        by bypr => &m0 hm0; rewrite /p; byequiv => //; proc (true).
      + by (conseq (_ : _ ==> false); 1:smt()); auto.
      smt().

    have Hfalse :
      Pr[
        FairApplicationBitRunner.main(root_bit) @ &m :
          res /\ ! FairApplicationBitRunner.sampled_bit
      ] =
      1%r / 2%r *
      Pr[
        G.main_with_root_and_application_bit(
          root_bit, false
        ) @ &m : res.`alae_authenticated_win
      ].
    + byphoare (_ :
          (glob G) = (glob G){m} /\ arg = root_bit
       ==>
          res /\ ! FairApplicationBitRunner.sampled_bit) => //.
      proc.
      pose p := Pr[
        G.main_with_root_and_application_bit(
          root_bit, false
        ) @ &m : res.`alae_authenticated_win
      ].
      seq 1 :
        (FairApplicationBitRunner.sampled_bit = false /\
         root_bit{hr} = root_bit)
        (1%r / 2%r) p _ 0%r
        ((glob G) = (glob G){m} /\ root_bit{hr} = root_bit);
        first by auto.
      + by rnd (pred1 false); skip => />; rewrite dbool1E.
      + if; first by (conseq (_ : false ==> _); 1:by smt()); auto.
        conseq (_ : _ ==> evidence.`alae_authenticated_win) => //;
          first by smt().
        call (_ :
          arg = (root_bit, false) /\ (glob G) = (glob G){m}
          ==> res.`alae_authenticated_win); last by auto.
        by bypr => &m0 hm0; rewrite /p; byequiv => //; proc (true).
      + by (conseq (_ : _ ==> false); 1:smt()); auto.
      smt().

    rewrite Htrue Hfalse.
    smt().
  qed.
end section AuthoritativeSampledApplicationNormalization.
