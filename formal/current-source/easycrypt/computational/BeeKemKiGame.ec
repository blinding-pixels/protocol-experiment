require import AllCore List FSet DBool DList.
require import BeeKemTypes BeeKemQueryLog BeeKemProtocol BeeKemSafety.

(* Figure 8's ideal branch is represented literally: draw a uniformly random
   bitstring of exactly the real group-secret length.  There is no adversary- or
   theorem-supplied sampler at this boundary. *)
module type BEEKEM_KI_ORACLES = {
  proc create_group(
    creator : beekem_user,
    initial_members : beekem_user fset
  ) : bool

  proc add_member(
    actor : beekem_user,
    target : beekem_user
  ) : bool

  proc remove_member(
    actor : beekem_user,
    target : beekem_user
  ) : bool

  proc send_update(actor : beekem_user) : bool

  proc deliver(
    sender : beekem_user,
    counter : beekem_counter,
    recipient : beekem_user
  ) : bool

  proc reveal(
    sender : beekem_user,
    counter : beekem_counter
  ) : beekem_secret_output

  proc challenge(
    sender : beekem_user,
    counter : beekem_counter
  ) : beekem_secret_output

  proc compromise(id : beekem_user) : beekem_member_state option

  (* Figure 8 gives the adversary perpetual read access to both message maps.
     Read procedures preserve that access without handing it mutable game state. *)
  proc get_control_message(
    sender : beekem_user,
    counter : beekem_counter
  ) : beekem_generated_message option

  proc get_direct_message(
    sender : beekem_user,
    counter : beekem_counter,
    recipient : beekem_user
  ) : beekem_direct_message option
}.

module type BEEKEM_KI_ADVERSARY(O : BEEKEM_KI_ORACLES) = {
  proc attack() : bool
}.

module BeeKemKiOracles(
  P : BEEKEM_PROTOCOL_ALGORITHMS
) = {
  module Environment = BeeKemOracleEnvironment(P)

  var hidden_bit : bool
  var real_branch_count : int
  var random_branch_count : int
  var random_sample_count : int

  proc initialize(
    users : beekem_user list,
    group : beekem_group,
    kappa : int,
    membership : beekem_dgm,
    bit : bool
  ) : unit = {
    hidden_bit <- bit;
    real_branch_count <- 0;
    random_branch_count <- 0;
    random_sample_count <- 0;
    Environment.initialize(users, group, kappa, membership);
  }

  proc create_group(
    creator : beekem_user,
    initial_members : beekem_user fset
  ) : bool = {
    var accepted : bool;
    accepted <@ Environment.create_group(creator, initial_members);
    return accepted;
  }

  proc add_member(
    actor : beekem_user,
    target : beekem_user
  ) : bool = {
    var accepted : bool;
    accepted <@ Environment.add_member(actor, target);
    return accepted;
  }

  proc remove_member(
    actor : beekem_user,
    target : beekem_user
  ) : bool = {
    var accepted : bool;
    accepted <@ Environment.remove_meber(
      actor, target
    );
    return accepted;
  }

  proc send_update(actor : beekem_user) : bool = {
    var accepted : bool;
    accepted <@ Environment.send_update(actor);
    return accepted;
  }

  proc deliver(
    sender : beekem_user,
    counter : beekem_counter,
    recipient : beekem_user
  ) : bool = {
    var accepted : bool;
    accepted <@ Environment.deliver(sender, counter, recipient);
    return accepted;
  }

  proc reveal(
    sender : beekem_user,
    counter : beekem_counter
  ) : beekem_secret_output = {
    var answer : beekem_secret_output;
    answer <@ Environment.reveal(sender, counter);
    return answer;
  }

  proc challenge(
    sender : beekem_user,
    counter : beekem_counter
  ) : beekem_secret_output = {
    var before_count : int;
    var after_count : int;
    var real_output : beekem_secret_output;
    var real_secret : beekem_group_secret;
    var real_bits : bool list;
    var random_bits : bool list;
    var random_secret : beekem_group_secret;
    var answer : beekem_secret_output;

    before_count <- Environment.state.`bps_challenge_count;
    real_output <@ Environment.open_challenge(sender, counter);
    after_count <- Environment.state.`bps_challenge_count;
    answer <- real_output;

    if (before_count < after_count) {
      if (hidden_bit) {
        real_branch_count <- real_branch_count + 1;
      } else {
        random_branch_count <- random_branch_count + 1;
        if (beekem_secret_output_is_value real_output) {
          real_secret <- oget (beekem_secret_output_value real_output);
          real_bits <- beekem_group_secret_bits real_secret;
          random_bits <$ dlist dbool (size real_bits);
          random_secret <- BeeKemGroupSecret random_bits;
          random_sample_count <- random_sample_count + 1;
          answer <- BeeSecretValue random_secret;
        }
      }
    }

    return answer;
  }

  proc compromise(id : beekem_user) : beekem_member_state option = {
    var answer : beekem_member_state option;
    answer <@ Environment.compromise(id);
    return answer;
  }

  proc get_control_message(
    sender : beekem_user,
    counter : beekem_counter
  ) : beekem_generated_message option = {
    return Environment.state.`bps_messages (sender, counter);
  }

  proc get_direct_message(
    sender : beekem_user,
    counter : beekem_counter,
    recipient : beekem_user
  ) : beekem_direct_message option = {
    return Environment.state.`bps_direct_messages
      (sender, counter, recipient);
  }
}.

op beekem_ki_final_win
    (safe protocol_failure adversary_guess hidden_bit : bool) : bool =
  safe /\ (protocol_failure \/ adversary_guess = hidden_bit).

type beekem_ki_evidence = {
  bke_hidden_bit : bool;
  bke_adversary_guess : bool;
  bke_safe : bool;
  bke_protocol_consistency_failure : bool;
  bke_challenge_count : int;
  bke_member_addition_count : int;
  bke_real_branch_count : int;
  bke_random_branch_count : int;
  bke_random_sample_count : int;
  bke_win : bool
}.

module BeeKemKiGame(
  A : BEEKEM_KI_ADVERSARY,
  P : BEEKEM_PROTOCOL_ALGORITHMS
) = {
  module O = BeeKemKiOracles(P)
  module A = A(O)

  var last_evidence : beekem_ki_evidence

  (* Deterministic branch runner used only by checker-proved non-vacuity and
     mutation witnesses.  [main_with_evidence] below still samples the hidden
     bit exactly as Figure 8 requires, then delegates to this same code path. *)
  proc main_with_fixed_bit(
    users : beekem_user list,
    group : beekem_group,
    kappa : int,
    membership : beekem_dgm,
    hidden_bit : bool
  ) : beekem_ki_evidence = {
    var guess : bool;
    var safe : bool;
    var protocol_failure : bool;
    var win : bool;

    O.initialize(users, group, kappa, membership, hidden_bit);
    guess <@ A.attack();

    safe <- bee_safe_kappa
      kappa
      O.Environment.state.`bps_operations
      O.Environment.query_log;
    protocol_failure <- O.Environment.protocol_consistency_failure;

    (* Figure 8 sets win on either a protocol-consistency failure or a correct
       final guess, and then clears it when the complete query trace is unsafe.
       Mutation games reuse this same operator and change only their named
       safety condition. *)
    win <- beekem_ki_final_win
      safe protocol_failure guess hidden_bit;

    last_evidence <-
      {| bke_hidden_bit = hidden_bit;
         bke_adversary_guess = guess;
         bke_safe = safe;
         bke_protocol_consistency_failure = protocol_failure;
         bke_challenge_count = O.Environment.state.`bps_challenge_count;
         bke_member_addition_count =
           O.Environment.state.`bps_member_addition_count;
         bke_real_branch_count = O.real_branch_count;
         bke_random_branch_count = O.random_branch_count;
         bke_random_sample_count = O.random_sample_count;
         bke_win = win |};
    return last_evidence;
  }

  proc main_with_evidence(
    users : beekem_user list,
    group : beekem_group,
    kappa : int,
    membership : beekem_dgm
  ) : beekem_ki_evidence = {
    var hidden_bit : bool;
    var evidence : beekem_ki_evidence;

    hidden_bit <$ dbool;
    evidence <@ main_with_fixed_bit(
      users, group, kappa, membership, hidden_bit
    );
    return evidence;
  }

  proc main(
    users : beekem_user list,
    group : beekem_group,
    kappa : int,
    membership : beekem_dgm
  ) : bool = {
    var evidence : beekem_ki_evidence;
    evidence <@ main_with_evidence(users, group, kappa, membership);
    return evidence.`bke_win;
  }
}.

(* The paper calls raw game-success probability its advantage.  Application
   composition uses the standard centered normalization.  Keeping this as a
   deterministic operator makes the convention difference explicit without
   changing the imported paper theorem. *)
op beekem_normalized_ki_advantage (success_probability : real) : real =
  if 1%r / 2%r <= success_probability
  then success_probability - 1%r / 2%r
  else 1%r / 2%r - success_probability.
