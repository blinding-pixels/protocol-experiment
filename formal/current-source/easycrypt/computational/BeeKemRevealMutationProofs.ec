require import AllCore List FSet.
require import BeeKemTypes BeeKemQueryLog BeeKemProtocol BeeKemSafety BeeKemKiGame.
require import BeeKemGameWitnesses.

(* Figure 8 enforces Reveal/Challenge exclusivity through the shared chal map,
   before the final P(queries) safety predicate.  The mutation below preserves
   the successful Reveal in the append-only log and changes only whether that
   entry contributes its shared admission mark to the later Challenge. *)
op beekem_successful_reveal_for
    (queries : beekem_query list)
    (sender : beekem_user)
    (counter : beekem_counter) : bool =
  with queries = [] => false
  with queries = query :: remaining =>
       (beekem_query_is_reveal query /\
        beekem_query_successful query /\
        query.`bq_actor = sender /\
        query.`bq_counter = Some counter)
    \/ beekem_successful_reveal_for remaining sender counter.

op beekem_successful_challenge_for
    (queries : beekem_query list)
    (sender : beekem_user)
    (counter : beekem_counter) : bool =
  with queries = [] => false
  with queries = query :: remaining =>
       (beekem_query_is_challenge query /\
        beekem_query_successful query /\
        query.`bq_actor = sender /\
        query.`bq_counter = Some counter)
    \/ beekem_successful_challenge_for remaining sender counter.

type beekem_reveal_mutation_evidence = {
  brme_hidden_bit : bool;
  brme_ignore_reveal_log : bool;
  brme_reveal_logged : bool;
  brme_challenge_logged : bool;
  brme_guess : bool;
  brme_safe : bool;
  brme_protocol_consistency_failure : bool;
  brme_challenge_count : int;
  brme_real_branch_count : int;
  brme_random_branch_count : int;
  brme_win : bool
}.

module BeeKemRevealAdmissionMutationGame = {
  module O = BeeKemKiOracles(BeeKemWitnessProtocol)

  (* This is a fixed witness adversary executed against the exact KI oracle.
     [ignore_reveal_log] is the single mutation control. *)
  proc main_with_fixed_mutation(
    hidden_bit : bool,
    ignore_reveal_log : bool
  ) : beekem_reveal_mutation_evidence = {
    var created : bool;
    var updated : bool;
    var revealed : beekem_secret_output;
    var challenged : beekem_secret_output;
    var reveal_logged : bool;
    var challenge_logged : bool;
    var guess : bool;
    var safe : bool;
    var protocol_failure : bool;
    var win : bool;

    O.initialize(
      [beekem_witness_user],
      beekem_witness_group,
      1,
      beekem_witness_membership,
      hidden_bit
    );
    created <@ O.create_group(beekem_witness_user, fset0);
    updated <@ O.send_update(beekem_witness_user);
    revealed <@ O.reveal(beekem_witness_user, BeeKemCounter 2);

    reveal_logged <- beekem_successful_reveal_for
      O.Environment.query_log beekem_witness_user (BeeKemCounter 2);
    if (ignore_reveal_log /\ reveal_logged) {
      O.Environment.state <-
        {| O.Environment.state with
           bps_challenge_marks =
             beekem_challenge_mark_map_set
               O.Environment.state.`bps_challenge_marks
               (beekem_witness_user, BeeKemCounter 2)
               false |};
    }

    challenged <@ O.challenge(beekem_witness_user, BeeKemCounter 2);
    challenge_logged <- beekem_successful_challenge_for
      O.Environment.query_log beekem_witness_user (BeeKemCounter 2);
    guess <- created /\ updated /\
      revealed = BeeSecretValue beekem_witness_real_secret /\
      challenged = BeeSecretValue beekem_witness_real_secret;
    safe <- bee_safe_kappa
      1 O.Environment.state.`bps_operations O.Environment.query_log;
    protocol_failure <- O.Environment.protocol_consistency_failure;
    win <- beekem_ki_final_win safe protocol_failure guess hidden_bit;

    return
      {| brme_hidden_bit = hidden_bit;
         brme_ignore_reveal_log = ignore_reveal_log;
         brme_reveal_logged = reveal_logged;
         brme_challenge_logged = challenge_logged;
         brme_guess = guess;
         brme_safe = safe;
         brme_protocol_consistency_failure = protocol_failure;
         brme_challenge_count = O.Environment.state.`bps_challenge_count;
         brme_real_branch_count = O.real_branch_count;
         brme_random_branch_count = O.random_branch_count;
         brme_win = win |};
  }
}.

lemma exact_reveal_log_blocks_actual_ki_challenge :
  hoare [BeeKemRevealAdmissionMutationGame.main_with_fixed_mutation :
       hidden_bit = true /\ ignore_reveal_log = false
    ==>
       res.`brme_hidden_bit
    /\ ! res.`brme_ignore_reveal_log
    /\ res.`brme_reveal_logged
    /\ ! res.`brme_challenge_logged
    /\ ! res.`brme_guess
    /\ res.`brme_safe
    /\ ! res.`brme_protocol_consistency_failure
    /\ res.`brme_challenge_count = 0
    /\ res.`brme_real_branch_count = 0
    /\ res.`brme_random_branch_count = 0
    /\ ! res.`brme_win].
proof.
  proc.
  inline *.
  rcondt ^while; first by auto.
  rcondf ^while; first by auto.
  rcondf ^while; first by auto.
  rcondt ^while; first by auto.
  rcondf ^while; first by auto.
  rcondf ^while; first by auto.
  auto.
  rewrite /beekem_witness_membership /beekem_witness_initial_member_state
    /beekem_member_retention_valid /beekem_witness_personal_secret
    /beekem_witness_after_create /beekem_witness_after_update
    /beekem_witness_control /beekem_witness_create_operation
    /beekem_witness_update_operation /beekem_witness_operation
    /beekem_control_operation_id /beekem_control_operation
    /beekem_counter_value /beekem_empty_protocol_state
    /beekem_challenge_mark_map_set
    /beekem_secret_output_is_undefined /beekem_secret_output_is_value
    /beekem_secret_output_value /beekem_operation_precedes_or_equals
    /beekem_operation_precedes /bee_safe_kappa /beekem_all_challenges_safe
    /beekem_challenge_safe_against /beekem_query_successful
    /beekem_query_is_reveal /beekem_query_is_challenge
    /beekem_query_is_compromise /beekem_successful_reveal_for
    /beekem_successful_challenge_for /beekem_ki_final_win.
  smt(in_fset0 in_fset1 size_rcons size_ge0).
qed.

lemma mutation_ignore_reveal_log_reaches_actual_ki_challenge :
  hoare [BeeKemRevealAdmissionMutationGame.main_with_fixed_mutation :
       hidden_bit = true /\ ignore_reveal_log = true
    ==>
       res.`brme_hidden_bit
    /\ res.`brme_ignore_reveal_log
    /\ res.`brme_reveal_logged
    /\ res.`brme_challenge_logged
    /\ res.`brme_guess
    /\ res.`brme_safe
    /\ ! res.`brme_protocol_consistency_failure
    /\ res.`brme_challenge_count = 1
    /\ res.`brme_real_branch_count = 1
    /\ res.`brme_random_branch_count = 0
    /\ res.`brme_win].
proof.
  proc.
  inline *.
  rcondt ^while; first by auto.
  rcondf ^while; first by auto.
  rcondf ^while; first by auto.
  rcondt ^while; first by auto.
  rcondf ^while; first by auto.
  rcondf ^while; first by auto.
  auto.
  rewrite /beekem_witness_membership /beekem_witness_initial_member_state
    /beekem_member_retention_valid /beekem_witness_personal_secret
    /beekem_witness_after_create /beekem_witness_after_update
    /beekem_witness_control /beekem_witness_create_operation
    /beekem_witness_update_operation /beekem_witness_operation
    /beekem_control_operation_id /beekem_control_operation
    /beekem_counter_value /beekem_empty_protocol_state
    /beekem_challenge_mark_map_set
    /beekem_secret_output_is_undefined /beekem_secret_output_is_value
    /beekem_secret_output_value /beekem_operation_precedes_or_equals
    /beekem_operation_precedes /bee_safe_kappa /beekem_all_challenges_safe
    /beekem_challenge_safe_against /beekem_query_successful
    /beekem_query_is_reveal /beekem_query_is_challenge
    /beekem_query_is_compromise /beekem_successful_reveal_for
    /beekem_successful_challenge_for /beekem_ki_final_win.
  smt(in_fset0 in_fset1 size_rcons size_ge0).
qed.
