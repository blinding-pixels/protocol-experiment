require import AllCore List FSet.
require import ProtocolTypes.
require import BeeKemTypes BeeKemQueryLog BeeKemSafety BeeKemKiGame.
require import BeeKemGameWitnesses.

(* Application-side carriers for the authoritative BeeKEM adapter.  These
   records do not restate the BeeKEM game.  They retain the cross-layer identity
   and addressing evidence that must be proved before an application node can
   call an authoritative reveal, challenge, delivery, or compromise oracle. *)
type application_user_registry = {
  aur_user_of : principal -> beekem_user option;
  aur_principal_of : beekem_user -> principal option
}.

(* EasyCrypt's finite-set library exposes singleton and union constructors, but
   no list conversion at this pinned revision.  This structural conversion is
   used only after every application principal has been mapped explicitly. *)
op oflist (members : beekem_user list) : beekem_user fset =
  with members = [] => fset0
  with members = member :: rest => fset1 member `|` oflist rest.

op empty_application_user_registry : application_user_registry =
  {| aur_user_of = fun _ => None;
     aur_principal_of = fun _ => None |}.

op application_user_registry_bind
    (registry : application_user_registry)
    (member : principal)
    (user : beekem_user) : application_user_registry =
  {| aur_user_of = fun candidate =>
       if candidate = member then Some user
       else registry.`aur_user_of candidate;
     aur_principal_of = fun candidate =>
       if candidate = user then Some member
       else registry.`aur_principal_of candidate |}.

op application_user_registry_fresh
    (registry : application_user_registry)
    (member : principal)
    (user : beekem_user) : bool =
  registry.`aur_user_of member = None /\
  registry.`aur_principal_of user = None.

op application_user_registry_round_trip
    (registry : application_user_registry) : bool =
  forall member user,
    registry.`aur_user_of member = Some user <=>
    registry.`aur_principal_of user = Some member.

op application_user_registry_injective
    (registry : application_user_registry) : bool =
  forall left right user,
    registry.`aur_user_of left = Some user =>
    registry.`aur_user_of right = Some user =>
    left = right.

lemma empty_application_user_registry_round_trip :
  application_user_registry_round_trip empty_application_user_registry.
proof. by rewrite /application_user_registry_round_trip
  /empty_application_user_registry /=. qed.

lemma application_user_registry_bind_round_trip
    (registry : application_user_registry)
    (member : principal)
    (user : beekem_user) :
  application_user_registry_round_trip registry =>
  application_user_registry_fresh registry member user =>
  application_user_registry_round_trip
    (application_user_registry_bind registry member user).
proof.
  rewrite /application_user_registry_round_trip
    /application_user_registry_fresh /application_user_registry_bind /=.
  move=> hregistry [hmember huser] candidate_member candidate_user.
  case (candidate_member = member) => hcm;
  case (candidate_user = user) => hcu; smt().
qed.

lemma application_user_registry_round_trip_implies_injective
    (registry : application_user_registry) :
  application_user_registry_round_trip registry =>
  application_user_registry_injective registry.
proof.
  rewrite /application_user_registry_round_trip
    /application_user_registry_injective.
  smt().
qed.

(* Document identifiers and BeeKEM group identifiers are distinct wrapper
   types.  The adapter uses an explicit constructor-preserving bijection rather
   than an unchecked cast. *)
op application_group_of_document
    (document : document_id) : beekem_group =
  with document = DocumentId value => BeeKemGroup value.

op application_document_of_group
    (group : beekem_group) : document_id =
  with group = BeeKemGroup value => DocumentId value.

lemma application_document_group_round_trip
    (document : document_id) :
  application_document_of_group
    (application_group_of_document document) = document.
proof. by case document. qed.

lemma application_group_document_round_trip
    (group : beekem_group) :
  application_group_of_document
    (application_document_of_group group) = group.
proof. by case group. qed.

lemma application_group_of_document_injective
    (left right : document_id) :
  application_group_of_document left =
  application_group_of_document right =>
  left = right.
proof. by case left; case right. qed.

type application_beekem_address = {
  aba_node : node_id;
  aba_principal : principal;
  aba_user : beekem_user;
  aba_counter : beekem_counter;
  aba_operation : beekem_operation_id
}.

type application_beekem_address_registry = {
  abar_by_node : node_id -> application_beekem_address option;
  abar_node_of_message : beekem_user -> beekem_counter -> node_id option;
  abar_node_of_operation : beekem_operation_id -> node_id option
}.

op empty_application_beekem_address_registry :
    application_beekem_address_registry =
  {| abar_by_node = fun _ => None;
     abar_node_of_message = fun _ _ => None;
     abar_node_of_operation = fun _ => None |}.

op application_beekem_address_registry_bind
    (registry : application_beekem_address_registry)
    (address : application_beekem_address) :
    application_beekem_address_registry =
  {| abar_by_node = fun candidate =>
       if candidate = address.`aba_node then Some address
       else registry.`abar_by_node candidate;
     abar_node_of_message = fun candidate_user candidate_counter =>
       if candidate_user = address.`aba_user /\
          candidate_counter = address.`aba_counter
       then Some address.`aba_node
       else registry.`abar_node_of_message candidate_user candidate_counter;
     abar_node_of_operation = fun candidate =>
       if candidate = address.`aba_operation then Some address.`aba_node
       else registry.`abar_node_of_operation candidate |}.

op application_beekem_address_fresh
    (registry : application_beekem_address_registry)
    (address : application_beekem_address) : bool =
  registry.`abar_by_node address.`aba_node = None /\
  registry.`abar_node_of_message
    address.`aba_user address.`aba_counter = None /\
  registry.`abar_node_of_operation address.`aba_operation = None.

lemma application_beekem_address_bind_exact
    (registry : application_beekem_address_registry)
    (address : application_beekem_address) :
  (application_beekem_address_registry_bind registry address).`abar_by_node
      address.`aba_node = Some address /\
  (application_beekem_address_registry_bind registry address).`abar_node_of_message
      address.`aba_user address.`aba_counter = Some address.`aba_node /\
  (application_beekem_address_registry_bind registry address).`abar_node_of_operation
      address.`aba_operation = Some address.`aba_node.
proof. by rewrite /application_beekem_address_registry_bind /=. qed.

(* The authoritative group secret is a bitstring.  The application adapter
   retains that exact bitstring in a distinct wrapper and records all three
   BeeKEM result cases.  No cast, integer surrogate, or option collapse occurs
   at this boundary. *)
type authoritative_application_root = [
  AuthoritativeApplicationRoot of bool list
].

type authoritative_application_root_result = [
  | AuthoritativeRootNoOutput
  | AuthoritativeRootUndefined
  | AuthoritativeRootValue of authoritative_application_root
].

op authoritative_application_root_of_beekem
    (secret : beekem_group_secret) : authoritative_application_root =
  with secret = BeeKemGroupSecret bits =>
    AuthoritativeApplicationRoot bits.

op authoritative_application_root_result_of_beekem
    (output : beekem_secret_output) :
    authoritative_application_root_result =
  with output = BeeSecretNoOutput => AuthoritativeRootNoOutput
  with output = BeeSecretUndefined => AuthoritativeRootUndefined
  with output = BeeSecretValue secret =>
    AuthoritativeRootValue
      (authoritative_application_root_of_beekem secret).

op authoritative_application_root_represents
    (secret : beekem_group_secret)
    (root : authoritative_application_root) : bool =
  root = authoritative_application_root_of_beekem secret.

lemma authoritative_application_root_of_beekem_injective
    (left right : beekem_group_secret) :
  authoritative_application_root_of_beekem left =
  authoritative_application_root_of_beekem right =>
  left = right.
proof. by case left; case right. qed.

lemma authoritative_root_result_preserves_no_output :
  authoritative_application_root_result_of_beekem BeeSecretNoOutput =
  AuthoritativeRootNoOutput.
proof. by done. qed.

lemma authoritative_root_result_preserves_undefined :
  authoritative_application_root_result_of_beekem BeeSecretUndefined =
  AuthoritativeRootUndefined.
proof. by done. qed.

lemma authoritative_root_result_preserves_value
    (secret : beekem_group_secret) :
  authoritative_application_root_result_of_beekem
    (BeeSecretValue secret) =
  AuthoritativeRootValue
    (authoritative_application_root_of_beekem secret).
proof. by done. qed.

(* Concrete adapter carriers used only for non-vacuity.  The cryptographic
   trace below is the canonical BeeKemKiGame witness, not the provisional live
   runtime. *)
op authoritative_adapter_witness_principal : principal =
  {| p_verification_key = VerificationKey 701;
     p_incarnation_nonce = IncarnationNonce 1 |}.

op authoritative_adapter_witness_document : document_id = DocumentId 702.

op authoritative_adapter_witness_registry : application_user_registry =
  application_user_registry_bind
    empty_application_user_registry
    authoritative_adapter_witness_principal
    beekem_witness_user.

op authoritative_adapter_witness_address : application_beekem_address =
  {| aba_node = NodeId 2;
     aba_principal = authoritative_adapter_witness_principal;
     aba_user = beekem_witness_user;
     aba_counter = BeeKemCounter 2;
     aba_operation = beekem_witness_update_id |}.

op authoritative_adapter_witness_addresses :
    application_beekem_address_registry =
  application_beekem_address_registry_bind
    empty_application_beekem_address_registry
    authoritative_adapter_witness_address.

type authoritative_adapter_witness_evidence = {
  aawe_user_round_trip : bool;
  aawe_group_round_trip : bool;
  aawe_address_exact : bool;
  aawe_root_case_exact : bool;
  aawe_beekem_safe : bool;
  aawe_challenge_count : int;
  aawe_member_addition_count : int;
  aawe_win : bool
}.

module AuthoritativeAdapterNonVacuity = {
  module G = BeeKemWitnessGame

  proc main() : authoritative_adapter_witness_evidence = {
    var evidence : beekem_ki_evidence;
    var user_round_trip : bool;
    var group_round_trip : bool;
    var address_exact : bool;
    var root_case_exact : bool;

    evidence <@ G.main_with_fixed_bit(
      [beekem_witness_user],
      application_group_of_document authoritative_adapter_witness_document,
      1,
      beekem_witness_membership,
      true
    );

    user_round_trip <-
      authoritative_adapter_witness_registry.`aur_user_of
        authoritative_adapter_witness_principal = Some beekem_witness_user /\
      authoritative_adapter_witness_registry.`aur_principal_of
        beekem_witness_user = Some authoritative_adapter_witness_principal;
    group_round_trip <-
      application_group_of_document authoritative_adapter_witness_document =
      beekem_witness_group;
    address_exact <-
      authoritative_adapter_witness_addresses.`abar_by_node (NodeId 2) =
        Some authoritative_adapter_witness_address /\
      authoritative_adapter_witness_addresses.`abar_node_of_message
        beekem_witness_user (BeeKemCounter 2) = Some (NodeId 2) /\
      authoritative_adapter_witness_addresses.`abar_node_of_operation
        beekem_witness_update_id = Some (NodeId 2);
    root_case_exact <-
      authoritative_application_root_result_of_beekem
        (BeeSecretValue beekem_witness_real_secret) =
      AuthoritativeRootValue (AuthoritativeApplicationRoot [true]);

    return
      {| aawe_user_round_trip = user_round_trip;
         aawe_group_round_trip = group_round_trip;
         aawe_address_exact = address_exact;
         aawe_root_case_exact = root_case_exact;
         aawe_beekem_safe = evidence.`bke_safe;
         aawe_challenge_count = evidence.`bke_challenge_count;
         aawe_member_addition_count = evidence.`bke_member_addition_count;
         aawe_win = evidence.`bke_win |};
  }
}.

lemma authoritative_adapter_nonvacuity :
  hoare [AuthoritativeAdapterNonVacuity.main : true ==>
       res.`aawe_user_round_trip
    /\ res.`aawe_group_round_trip
    /\ res.`aawe_address_exact
    /\ res.`aawe_root_case_exact
    /\ res.`aawe_beekem_safe
    /\ res.`aawe_challenge_count = 1
    /\ res.`aawe_member_addition_count = 0
    /\ res.`aawe_win].
proof.
  proc.
  call beekem_witness_real_branch_reachable.
  auto.
  rewrite /authoritative_adapter_witness_registry
    /application_user_registry_bind
    /empty_application_user_registry
    /authoritative_adapter_witness_addresses
    /authoritative_adapter_witness_address
    /application_beekem_address_registry_bind
    /empty_application_beekem_address_registry
    /authoritative_application_root_result_of_beekem
    /authoritative_application_root_of_beekem
    /authoritative_adapter_witness_principal
    /authoritative_adapter_witness_document
    /application_group_of_document
    /beekem_witness_group /beekem_witness_user
    /beekem_witness_update_id /beekem_witness_real_secret /=.
  by done.
qed.
