require import AllCore List FSet.
require import ProtocolTypes CanonicalEncoding PrimitiveGames AuthorizationState.
require import ProtocolChecks ProtocolOracles.

(* The adversary receives only the stateful submission oracle. It controls the
   operation bytes and signatures it submits, but it cannot set validation,
   causal closure, or the unauthorized-acceptance event. *)
module type UNAUTHORIZED_ADVERSARY(O : SUBMIT_OPERATION_ORACLE) = {
  proc attack() : unit
}.

module UnauthorizedReal(
  A : UNAUTHORIZED_ADVERSARY,
  S : SIGNATURE_SCHEME,
  H : NODE_HASH
) = {
  module O = ProtocolEnvironment(S, H)
  module A = A(O)

  proc main(
    initial_state : protocol_state,
    initial_facts : signed_authorization_fact list
  ) : bool = {
    O.init(Production, initial_state, initial_facts);
    A.attack();
    return O.unauthorized_accepted;
  }
}.

(* A differential environment runs the same submitted operation through the
   production validator and through the validator with exactly one defense
   removed. Both environments start from the same state and receive the same
   adaptive sequence of submissions. The witness event is set only when the
   mutated validator accepts an operation rejected by production. *)
module DifferentialEnvironment(
  S : SIGNATURE_SCHEME,
  H : NODE_HASH
) = {
  module ProductionEnvironment = ProtocolEnvironment(S, H)
  module MutatedEnvironment = ProtocolEnvironment(S, H)

  var removed_defense : defense
  var differential_win : bool
  var query_count : int

  proc init(
    removed : defense,
    initial_state : protocol_state,
    initial_facts : signed_authorization_fact list
  ) : unit = {
    removed_defense <- removed;
    differential_win <- false;
    query_count <- 0;
    ProductionEnvironment.init(Production, initial_state, initial_facts);
    MutatedEnvironment.init(
      WithoutDefense removed,
      initial_state,
      initial_facts
    );
  }

  proc submit(operation : signed_operation) : bool = {
    var production_accepted : bool;
    var mutated_accepted : bool;

    production_accepted <@ ProductionEnvironment.submit(operation);
    mutated_accepted <@ MutatedEnvironment.submit(operation);

    query_count <- query_count + 1;
    differential_win <-
      differential_win \/
      (mutated_accepted /\ ! production_accepted);

    return mutated_accepted;
  }
}.

module OneDefenseRemoved(
  A : UNAUTHORIZED_ADVERSARY,
  S : SIGNATURE_SCHEME,
  H : NODE_HASH
) = {
  module O = DifferentialEnvironment(S, H)
  module A = A(O)

  proc main(
    removed : defense,
    initial_state : protocol_state,
    initial_facts : signed_authorization_fact list
  ) : bool = {
    O.init(removed, initial_state, initial_facts);
    A.attack();
    return O.differential_win;
  }
}.

(* The query counter is part of the game state so mutation witnesses can show
   that the primitive/validator oracle was actually invoked rather than winning
   through an unreachable or constant branch. *)
module OneDefenseRemovedWithQueryEvidence(
  A : UNAUTHORIZED_ADVERSARY,
  S : SIGNATURE_SCHEME,
  H : NODE_HASH
) = {
  module O = DifferentialEnvironment(S, H)
  module A = A(O)

  proc main(
    removed : defense,
    initial_state : protocol_state,
    initial_facts : signed_authorization_fact list
  ) : bool * int = {
    O.init(removed, initial_state, initial_facts);
    A.attack();
    return (O.differential_win, O.query_count);
  }
}.
