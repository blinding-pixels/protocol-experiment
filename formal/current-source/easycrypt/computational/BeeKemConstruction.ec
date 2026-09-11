require import AllCore List FSet Distr.
require import BeeKemTypes BeeKemProtocol BeeKemPrimitiveGames.

(* Generic procedural surface for construction adapters and test fixtures.
   Having this type alone does NOT establish that a module is BeeKEM[SE,NIKE].
   The imported theorem below uses only PublishedBeeKemInstance, the named
   opaque paper primitive defined at the end of this file. *)
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

(* The imported theorem is about ONE named paper construction, not every
   module having BEEKEM_PAPER_INSTANCE's procedure types. These opaque
   transition distributions are the imported BeeKEM[SE, NIKE] algorithms and
   its own NIKE/SE primitives. Their cryptographic theorem remains the single
   explicit axiom in BeeKemKiInterface; no application theorem is imported.
   The executable KI game, query log, counters and safety checks are unchanged.

   General adapters and concrete diagnostic instances remain available above,
   but a diagnostic implementation cannot be substituted for this construction
   merely by inhabiting a module type. A concrete implementation refinement is
   a separate obligation, not something asserted by this abstract interface. *)

op published_protocol_init (id : beekem_user) (group : beekem_group) (kappa : int) : (beekem_member_state) distr.
op published_protocol_create (state : beekem_member_state) (initial_members : beekem_user fset) : (beekem_protocol_result) distr.
op published_protocol_add (state : beekem_member_state) (target : beekem_user) : (beekem_protocol_result) distr.
op published_protocol_remove_member (state : beekem_member_state) (target : beekem_user) : (beekem_protocol_result) distr.
op published_protocol_update (state : beekem_member_state) : (beekem_protocol_result) distr.
op published_protocol_process (state : beekem_member_state) (sender : beekem_user) (control : beekem_generated_message) (direct : beekem_direct_message option) : (beekem_process_result) distr.
op published_nike_keygen  : (beekem_public_key * beekem_secret_key) distr.
op published_nike_shared_key (public_key : beekem_public_key) (secret_key : beekem_secret_key) : (beekem_symmetric_key) distr.
op published_nike_sample  : (beekem_symmetric_key) distr.
op published_se_keygen  : (beekem_symmetric_key) distr.
op published_se_encrypt (key : beekem_symmetric_key) (message : beekem_secret_key) : (beekem_ciphertext) distr.
op published_se_decrypt (key : beekem_symmetric_key) (ciphertext : beekem_ciphertext) : (beekem_secret_key option) distr.

module PublishedBeeKemInstance : BEEKEM_PAPER_INSTANCE = {
  proc protocol_init(id : beekem_user,
    group : beekem_group,
    kappa : int) : beekem_member_state = {
    var result : beekem_member_state;
    result <$ published_protocol_init id group kappa;
    return result;
  }

  proc protocol_create(state : beekem_member_state,
    initial_members : beekem_user fset) : beekem_protocol_result = {
    var result : beekem_protocol_result;
    result <$ published_protocol_create state initial_members;
    return result;
  }

  proc protocol_add(state : beekem_member_state,
    target : beekem_user) : beekem_protocol_result = {
    var result : beekem_protocol_result;
    result <$ published_protocol_add state target;
    return result;
  }

  proc protocol_remove_member(state : beekem_member_state,
    target : beekem_user) : beekem_protocol_result = {
    var result : beekem_protocol_result;
    result <$ published_protocol_remove_member state target;
    return result;
  }

  proc protocol_update(state : beekem_member_state) : beekem_protocol_result = {
    var result : beekem_protocol_result;
    result <$ published_protocol_update state;
    return result;
  }

  proc protocol_process(state : beekem_member_state,
    sender : beekem_user,
    control : beekem_generated_message,
    direct : beekem_direct_message option) : beekem_process_result = {
    var result : beekem_process_result;
    result <$ published_protocol_process state sender control direct;
    return result;
  }

  proc nike_keygen() : beekem_public_key * beekem_secret_key = {
    var result : beekem_public_key * beekem_secret_key;
    result <$ published_nike_keygen ;
    return result;
  }

  proc nike_shared_key(public_key : beekem_public_key,
    secret_key : beekem_secret_key) : beekem_symmetric_key = {
    var result : beekem_symmetric_key;
    result <$ published_nike_shared_key public_key secret_key;
    return result;
  }

  proc nike_sample() : beekem_symmetric_key = {
    var result : beekem_symmetric_key;
    result <$ published_nike_sample ;
    return result;
  }

  proc se_keygen() : beekem_symmetric_key = {
    var result : beekem_symmetric_key;
    result <$ published_se_keygen ;
    return result;
  }

  proc se_encrypt(key : beekem_symmetric_key,
    message : beekem_secret_key) : beekem_ciphertext = {
    var result : beekem_ciphertext;
    result <$ published_se_encrypt key message;
    return result;
  }

  proc se_decrypt(key : beekem_symmetric_key,
    ciphertext : beekem_ciphertext) : beekem_secret_key option = {
    var result : beekem_secret_key option;
    result <$ published_se_decrypt key ciphertext;
    return result;
  }
}.
