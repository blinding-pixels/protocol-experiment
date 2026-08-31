require import AllCore List.
require import LiveKeyGame BeeKemTypes.
require import LiveBeeKemAuthoritativeTypes.

(* Concrete, prefix-free representation of BeeKEM's bitstring group secret in
   the existing application key-schedule carrier.  The empty bitstring maps to
   zero; each non-empty list records both its head bit and a continuation tag,
   so no carrier cast or length-forgetting conversion occurs. *)
op authoritative_application_root_code (bits : bool list) : int =
  with bits = [] => 0
  with bits = bit :: rest =>
    (if bit then 2 else 1) + 2 * authoritative_application_root_code rest.

op application_beekem_root_of_authoritative
    (root : authoritative_application_root) : beekem_secret =
  with root = AuthoritativeApplicationRoot bits =>
    BeeKemSecret (authoritative_application_root_code bits).

op application_beekem_root_represents
    (authoritative : authoritative_application_root)
    (application : beekem_secret) : bool =
  application = application_beekem_root_of_authoritative authoritative.

(* The bridge itself retains all three Figure-8 output cases.  Only the Value
   constructor contains an application key-schedule root; NoOutput and
   Undefined remain distinguishable and are never silently converted to a
   secret option. *)
type application_beekem_root_bridge_result = [
  | ApplicationRootNoOutput
  | ApplicationRootUndefined
  | ApplicationRootValue of beekem_secret
].

op application_beekem_root_bridge
    (output : beekem_secret_output) :
    application_beekem_root_bridge_result =
  with output = BeeSecretNoOutput => ApplicationRootNoOutput
  with output = BeeSecretUndefined => ApplicationRootUndefined
  with output = BeeSecretValue secret =>
    ApplicationRootValue
      (application_beekem_root_of_authoritative
        (authoritative_application_root_of_beekem secret)).

lemma authoritative_application_root_code_nonnegative
    (bits : bool list) :
  0 <= authoritative_application_root_code bits.
proof.
  elim: bits => [| bit rest ih] //=.
  by case: bit; smt().
qed.

lemma application_beekem_root_bridge_no_output :
  application_beekem_root_bridge BeeSecretNoOutput =
  ApplicationRootNoOutput.
proof. by done. qed.

lemma application_beekem_root_bridge_undefined :
  application_beekem_root_bridge BeeSecretUndefined =
  ApplicationRootUndefined.
proof. by done. qed.

lemma application_beekem_root_bridge_value
    (secret : beekem_group_secret) :
  application_beekem_root_bridge (BeeSecretValue secret) =
  ApplicationRootValue
    (application_beekem_root_of_authoritative
      (authoritative_application_root_of_beekem secret)).
proof. by done. qed.

lemma application_beekem_root_bridge_cases_distinct :
  ApplicationRootNoOutput <> ApplicationRootUndefined /\
  (forall root, ApplicationRootNoOutput <> ApplicationRootValue root) /\
  (forall root, ApplicationRootUndefined <> ApplicationRootValue root).
proof. by done. qed.

lemma authoritative_application_witness_root_bridge_exact :
  application_beekem_root_bridge
    (BeeSecretValue (BeeKemGroupSecret [true])) =
  ApplicationRootValue (BeeKemSecret 2).
proof.
  by rewrite /application_beekem_root_bridge
    /authoritative_application_root_of_beekem
    /application_beekem_root_of_authoritative
    /authoritative_application_root_code.
qed.
