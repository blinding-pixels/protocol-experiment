require import AllCore List FSet.
require import ProtocolTypes ProtocolChecks CanonicalEncoding.
require import LiveKeyGame LivePrfTypes LivePrfGame.
require import LivePrfControls LivePrfIdeal.

module IdealPrfControl = MultiDomainPrfIdealProjection(
  InsecureKdfPrfAdversary,
  TestMultiDomainKeySchedule,
  TestLiveKeySampler
).

(* Non-vacuity control for ideal zero.  The same adversary used to distinguish
   the insecure real KDF actually executes one real-only live reveal, one
   history query, one constrained-history query, and one sampled live challenge
   in the bit-free ideal oracle.  The reveal is real and the challenge is
   sampled, so the adversary is eligible and guesses false; zero advantage is
   therefore caused by bit independence, not by skipping an oracle path or
   forcing ineligibility. *)
lemma ideal_control_reaches_all_domains :
  hoare [IdealPrfControl.main :
       true
    ==>
       res.`mpar_eligible
    /\ ! res.`mpar_guess
    /\ mdprf_live_query_count IdealPrfControl.O.queries = 1
    /\ mdprf_live_challenge_count IdealPrfControl.O.queries = 1
    /\ mdprf_history_query_count IdealPrfControl.O.queries = 1
    /\ mdprf_history_capability_query_count
         IdealPrfControl.O.queries = 1].
proof. by proc; inline *; auto. qed.
