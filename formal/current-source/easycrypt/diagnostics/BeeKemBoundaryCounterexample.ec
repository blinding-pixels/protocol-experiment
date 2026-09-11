require import AllCore List FSet Distr DBool.
require import BeeKemTypes BeeKemProtocol BeeKemSafety BeeKemKiGame.
require import BeeKemGameWitnesses BeeKemPrimitiveWitnesses.
require import BeeKemConstruction BeeKemPrimitiveContracts BeeKemTheorem1Math.

(* Diagnostic only. No security axiom is imported here. All procedure bodies
   below are aliases to existing concrete witness implementations. *)
module BoundaryDiagnosticInstance : BEEKEM_PAPER_INSTANCE = {
  proc protocol_init = BeeKemWitnessProtocol.init
  proc protocol_create = BeeKemWitnessProtocol.create
  proc protocol_add = BeeKemWitnessProtocol.add
  proc protocol_remove_member = BeeKemWitnessProtocol.remove_member
  proc protocol_update = BeeKemWitnessProtocol.update
  proc protocol_process = BeeKemWitnessProtocol.process
  proc nike_keygen = BeeKemInsecureNike.keygen
  proc nike_shared_key = BeeKemInsecureNike.shared_key
  proc nike_sample = BeeKemInsecureNikeRandom.sample
  proc se_keygen = BeeKemInsecureSe.keygen
  proc se_encrypt = BeeKemInsecureSe.encrypt
  proc se_decrypt = BeeKemInsecureSe.decrypt
}.
module BoundaryDiagnosticProtocol = BeeKemProtocolOfPaperInstance(BoundaryDiagnosticInstance).
module BoundaryDiagnosticOracle = BeeKemKiOracles(BoundaryDiagnosticProtocol).

(* This implementation satisfies the declared module type. It exposes the
   difference between that unrestricted type and oracle-only access. *)
module BoundaryHiddenBitReader(O : BEEKEM_KI_ORACLES) = {
  proc attack() : bool = { return BoundaryDiagnosticOracle.hidden_bit; }
}.
module BoundaryLeakGame = BeeKemKiGame(BoundaryHiddenBitReader, BoundaryDiagnosticProtocol).

lemma boundary_reader_fixed_bit :
  phoare [BoundaryLeakGame.main_with_fixed_bit :
    users = [] /\ kappa = 1 ==>
    res.`bke_safe /\ res.`bke_win /\
    res.`bke_challenge_count = 0 /\ res.`bke_member_addition_count = 0 /\
    ! res.`bke_protocol_consistency_failure] = 1%r.
proof.
  proc; inline *.
  rcondf ^while; first by auto.
  by auto=> />; cbv delta.
qed.

lemma boundary_reader_sampled_bit :
  phoare [BoundaryLeakGame.main_with_evidence :
    users = [] /\ kappa = 1 ==>
    res.`bke_safe /\ res.`bke_win /\
    res.`bke_challenge_count = 0 /\ res.`bke_member_addition_count = 0 /\
    ! res.`bke_protocol_consistency_failure] = 1%r.
proof.
  proc; inline *.
  rcondf ^while; first by auto.
  by auto=> />; cbv delta; rewrite dbool_ll.
qed.

module BoundaryNikeSymmetry = BeeKemNikeSymmetryGame(BeeKemNikeOfPaperInstance(BoundaryDiagnosticInstance)).
module BoundarySeCorrectness = BeeKemSeCorrectnessGame(BeeKemSeOfPaperInstance(BoundaryDiagnosticInstance)).

lemma boundary_nike_symmetry &m :
  Pr[BoundaryNikeSymmetry.main() @ &m : res] = 1%r.
proof. byphoare => //; proc; inline *; auto. qed.

lemma boundary_se_correctness &m (message : beekem_secret_key) :
  Pr[BoundarySeCorrectness.main(message) @ &m : res] = 1%r.
proof.
  byphoare => //.
  proc; inline *; auto.
  move=> &hr _.
  case (message{!hr}) => value.
  by rewrite /beekem_insecure_ciphertext_of /beekem_insecure_plaintext_of.
qed.

lemma boundary_all_safe &m (group : beekem_group) (membership : beekem_dgm) :
  Pr[BoundaryLeakGame.main_with_evidence([], group, 1, membership) @ &m :
    res.`bke_safe] = 1%r.
proof.
  byphoare (_ : users = [] /\ kappa = 1 ==> res.`bke_safe) => //.
  proc; inline *.
  rcondf ^while; first by auto.
  by auto=> />; cbv delta; rewrite dbool_ll.
qed.

lemma boundary_counters_zero &m (group : beekem_group) (membership : beekem_dgm) :
  Pr[BoundaryLeakGame.main_with_evidence([], group, 1, membership) @ &m :
    res.`bke_challenge_count <= 0 /\ res.`bke_member_addition_count <= 2] = 1%r.
proof.
  byphoare (_ : users = [] /\ kappa = 1 ==>
    res.`bke_challenge_count <= 0 /\ res.`bke_member_addition_count <= 2) => //.
  proc; inline *.
  rcondf ^while; first by auto.
  by auto=> />; cbv delta; rewrite dbool_ll.
qed.

lemma boundary_win_probability_one &m (group : beekem_group) (membership : beekem_dgm) :
  Pr[BoundaryLeakGame.main([], group, 1, membership) @ &m : res] = 1%r.
proof.
  byphoare (_ : users = [] /\ kappa = 1 ==> res) => //.
  proc; inline *.
  rcondf ^while; first by auto.
  by auto=> />; cbv delta; rewrite dbool_ll.
qed.

lemma boundary_advantage_half &m (group : beekem_group) (membership : beekem_dgm) :
  beekem_normalized_ki_advantage
    (Pr[BoundaryLeakGame.main([], group, 1, membership) @ &m : res]) = 1%r / 2%r.
proof.
  rewrite boundary_win_probability_one /beekem_normalized_ki_advantage.
  smt().
qed.

(* This refutes the zero-challenge conclusion for every real RHS value, not
   merely for a particular pair of primitive reduction witnesses. *)
lemma boundary_refutes_every_primitive_loss &m
    (group : beekem_group) (membership : beekem_dgm) (primitive_loss : real) :
  ! (beekem_normalized_ki_advantage
       (Pr[BoundaryLeakGame.main([], group, 1, membership) @ &m : res])
     <= beekem_theorem1_loss 0 1 * primitive_loss).
proof.
  rewrite boundary_advantage_half /beekem_theorem1_loss.
  smt().
qed.

(* The same issue occurs with an initialized member, so it is not specific
   to the empty-user input used by the minimal counterexample. *)
lemma boundary_nonempty_all_safe &m (group : beekem_group) (membership : beekem_dgm) :
  Pr[BoundaryLeakGame.main_with_evidence([beekem_witness_user], group, 1, membership) @ &m :
    res.`bke_safe] = 1%r.
proof.
  byphoare (_ : users = [beekem_witness_user] /\ kappa = 1 ==> res.`bke_safe) => //.
  proc; inline *.
  rcondt ^while; first by auto.
  rcondf ^while; first by auto.
  by auto=> />; cbv delta; rewrite dbool_ll.
qed.

lemma boundary_nonempty_counters_zero &m (group : beekem_group) (membership : beekem_dgm) :
  Pr[BoundaryLeakGame.main_with_evidence([beekem_witness_user], group, 1, membership) @ &m :
    res.`bke_challenge_count <= 0 /\ res.`bke_member_addition_count <= 2] = 1%r.
proof.
  byphoare (_ : users = [beekem_witness_user] /\ kappa = 1 ==>
    res.`bke_challenge_count <= 0 /\ res.`bke_member_addition_count <= 2) => //.
  proc; inline *.
  rcondt ^while; first by auto.
  rcondf ^while; first by auto.
  by auto=> />; cbv delta; rewrite dbool_ll.
qed.

lemma boundary_nonempty_win_probability_one &m (group : beekem_group) (membership : beekem_dgm) :
  Pr[BoundaryLeakGame.main([beekem_witness_user], group, 1, membership) @ &m : res] = 1%r.
proof.
  byphoare (_ : users = [beekem_witness_user] /\ kappa = 1 ==> res) => //.
  proc; inline *.
  rcondt ^while; first by auto.
  rcondf ^while; first by auto.
  by auto=> />; cbv delta; rewrite dbool_ll.
qed.

lemma boundary_nonempty_advantage_half &m (group : beekem_group) (membership : beekem_dgm) :
  beekem_normalized_ki_advantage
    (Pr[BoundaryLeakGame.main([beekem_witness_user], group, 1, membership) @ &m : res]) = 1%r / 2%r.
proof.
  rewrite boundary_nonempty_win_probability_one /beekem_normalized_ki_advantage.
  smt().
qed.

module BoundaryConstantGuess(O : BEEKEM_KI_ORACLES) = {
  proc attack() : bool = { return false; }
}.
module BoundaryConstantGame = BeeKemKiGame(BoundaryConstantGuess, BoundaryDiagnosticProtocol).

lemma boundary_constant_guess_is_fair &m
    (group : beekem_group) (membership : beekem_dgm) :
  Pr[BoundaryConstantGame.main([], group, 1, membership) @ &m : res] = 1%r / 2%r.
proof.
  byphoare (_ : users = [] /\ kappa = 1 ==> res) => //.
  proc; inline *.
  rcondf ^while; first by auto.
  wp.
  rnd (pred1 false).
  auto=> />; cbv delta.
  by rewrite dbool1E.
qed.

(* The corrected named paper primitive has the ordinary fair baseline in the
   no-query, empty-initial-user experiment. This proof imports no security
   axiom and does not constrain the opaque published algorithms. *)
module BoundaryPublishedConstantGame =
  BeeKemKiGame(BoundaryConstantGuess,
    BeeKemProtocolOfPaperInstance(PublishedBeeKemInstance)).

lemma boundary_published_constant_guess_is_fair &m
    (group : beekem_group) (membership : beekem_dgm) :
  Pr[BoundaryPublishedConstantGame.main([], group, 1, membership) @ &m : res] = 1%r / 2%r.
proof.
  byphoare (_ : users = [] /\ kappa = 1 ==> res) => //.
  proc; inline *.
  rcondf ^while; first by auto.
  wp.
  rnd (pred1 false).
  auto=> />; cbv delta.
  by rewrite dbool1E.
qed.
