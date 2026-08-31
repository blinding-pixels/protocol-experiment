require import AllCore List FSet.
require import BeeKemTypes BeeKemProtocol BeeKemPrimitiveGames.

(* Theorem 1 is about the concrete construction BeeKEM[SE, NIKE], not an
   arbitrary protocol sharing only the DCGKA procedure surface.  EasyCrypt's
   current clone substitution crashes on a declared higher-order module, so the
   imported construction is represented by one flat module instance containing
   both the protocol procedures and the exact primitive procedures used by the
   right-hand-side games.

   This interface is intentionally stronger than three independent module
   parameters: every adapter below is definitionally backed by the same
   [BEEKEM_PAPER_INSTANCE].  The algorithm bodies and Appendix-B reductions are
   still imported paper evidence, not machine-checked implementations. *)
module type BEEKEM_PAPER_INSTANCE = {
  proc protocol_init(
    id : beekem_user,
    group : beekem_group,
    kappa : int
  ) : beekem_member_state

  proc protocol_create(
    state : beekem_member_state,
    initial_members : beekem_user fset
  ) : beekem_protocol_result

  proc protocol_add(
    state : beekem_member_state,
    target : beekem_user
  ) : beekem_protocol_result

  proc protocol_remove_member(
    state : beekem_member_state,
    target : beekem_user
  ) : beekem_protocol_result

  proc protocol_update(
    state : beekem_member_state
  ) : beekem_protocol_result

  proc protocol_process(
    state : beekem_member_state,
    sender : beekem_user,
    control : beekem_generated_message,
    direct : beekem_direct_message option
  ) : beekem_process_result

  proc nike_keygen() : beekem_public_key * beekem_secret_key

  proc nike_shared_key(
    public_key : beekem_public_key,
    secret_key : beekem_secret_key
  ) : beekem_symmetric_key

  proc nike_sample() : beekem_symmetric_key

  proc se_keygen() : beekem_symmetric_key

  proc se_encrypt(
    key : beekem_symmetric_key,
    message : beekem_secret_key
  ) : beekem_ciphertext

  proc se_decrypt(
    key : beekem_symmetric_key,
    ciphertext : beekem_ciphertext
  ) : beekem_secret_key option
}.

module BeeKemProtocolOfPaperInstance(
  I : BEEKEM_PAPER_INSTANCE
) : BEEKEM_PROTOCOL_ALGORITHMS = {
  proc init(
    id : beekem_user,
    group : beekem_group,
    kappa : int
  ) : beekem_member_state = {
    var result : beekem_member_state;
    result <@ I.protocol_init(id, group, kappa);
    return result;
  }

  proc create(
    state : beekem_member_state,
    initial_members : beekem_user fset
  ) : beekem_protocol_result = {
    var result : beekem_protocol_result;
    result <@ I.protocol_create(state, initial_members);
    return result;
  }

  proc add(
    state : beekem_member_state,
    target : beekem_user
  ) : beekem_protocol_result = {
    var result : beekem_protocol_result;
    result <@ I.protocol_add(state, target);
    return result;
  }

  proc remove_member(
    state : beekem_member_state,
    target : beekem_user
  ) : beekem_protocol_result = {
    var result : beekem_protocol_result;
    result <@ I.protocol_remove_member(state, target);
    return result;
  }

  proc update(
    state : beekem_member_state
  ) : beekem_protocol_result = {
    var result : beekem_protocol_result;
    result <@ I.protocol_update(state);
    return result;
  }

  proc process(
    state : beekem_member_state,
    sender : beekem_user,
    control : beekem_generated_message,
    direct : beekem_direct_message option
  ) : beekem_process_result = {
    var result : beekem_process_result;
    result <@ I.protocol_process(state, sender, control, direct);
    return result;
  }
}.

module BeeKemNikeOfPaperInstance(
  I : BEEKEM_PAPER_INSTANCE
) : BEEKEM_NIKE = {
  proc keygen() : beekem_public_key * beekem_secret_key = {
    var result : beekem_public_key * beekem_secret_key;
    result <@ I.nike_keygen();
    return result;
  }

  proc shared_key(
    public_key : beekem_public_key,
    secret_key : beekem_secret_key
  ) : beekem_symmetric_key = {
    var result : beekem_symmetric_key;
    result <@ I.nike_shared_key(public_key, secret_key);
    return result;
  }
}.

module BeeKemNikeSamplerOfPaperInstance(
  I : BEEKEM_PAPER_INSTANCE
) : BEEKEM_NIKE_KEY_SAMPLER = {
  proc sample() : beekem_symmetric_key = {
    var result : beekem_symmetric_key;
    result <@ I.nike_sample();
    return result;
  }
}.

module BeeKemSeOfPaperInstance(
  I : BEEKEM_PAPER_INSTANCE
) : BEEKEM_SYMMETRIC_ENCRYPTION = {
  proc keygen() : beekem_symmetric_key = {
    var result : beekem_symmetric_key;
    result <@ I.se_keygen();
    return result;
  }

  proc encrypt(
    key : beekem_symmetric_key,
    message : beekem_secret_key
  ) : beekem_ciphertext = {
    var result : beekem_ciphertext;
    result <@ I.se_encrypt(key, message);
    return result;
  }

  proc decrypt(
    key : beekem_symmetric_key,
    ciphertext : beekem_ciphertext
  ) : beekem_secret_key option = {
    var result : beekem_secret_key option;
    result <@ I.se_decrypt(key, ciphertext);
    return result;
  }
}.
