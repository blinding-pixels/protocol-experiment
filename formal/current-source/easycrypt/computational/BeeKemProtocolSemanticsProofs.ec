require import AllCore List FSet.
require import BeeKemTypes.

(* These lemmas pin the Figure 8 epsilon/bottom distinction and the finite-kappa
   state contract into the public checker closure. *)
lemma beekem_no_output_is_not_undefined :
  ! beekem_secret_output_is_undefined BeeSecretNoOutput.
proof. by rewrite /beekem_secret_output_is_undefined. qed.

lemma beekem_undefined_is_not_no_output :
  ! beekem_secret_output_is_no_output BeeSecretUndefined.
proof. by rewrite /beekem_secret_output_is_no_output. qed.

lemma beekem_value_is_not_undefined (secret : beekem_group_secret) :
  ! beekem_secret_output_is_undefined (BeeSecretValue secret).
proof. by rewrite /beekem_secret_output_is_undefined. qed.

lemma beekem_empty_secret_entry_is_undefined
    (group : beekem_group) (kappa : int) (key : beekem_message_key) :
  (beekem_empty_protocol_state group kappa).`bps_secrets key =
    BeeSecretUndefined.
proof. by rewrite /beekem_empty_protocol_state. qed.

lemma beekem_retention_requires_positive_kappa
    (kappa : int) (member_state : beekem_member_state) :
  beekem_member_retention_valid kappa member_state => 1 <= kappa.
proof. by rewrite /beekem_member_retention_valid => -[]. qed.
