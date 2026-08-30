require import LivePrfTypes.
require import LivePrfGame.
require import LivePrfExecutableNormalization.
require import LivePrfApplicationReduction.
require import LivePrfApplicationHop.
require import LivePrfApplicationControls.
require import LivePrfIdeal.
require import LivePrfControls.
require import LivePrfIdealControls.

require import LivePrfLabelBinding.
require import LivePrfDomainSeparationControls.
require import LivePrfCapabilityDomainSeparationControls.

(* Public aggregation point for the application multi-domain PRF checkpoint.
   The authoritative BeeKEM adapter remains an explicit later obligation. *)

print LivePrfExecutableNormalization.mdprf_sampled_game_equiv_fair_bit_runner.
print LivePrfExecutableNormalization.mdprf_sampled_win_probability_is_fixed_bit_average.
