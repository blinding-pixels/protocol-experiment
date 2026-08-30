require import AllCore List FSet.
require import BeeKemTypes BeeKemProtocol BeeKemPrimitiveGames.

(* Theorem 1 is about the concrete construction BeeKEM[SE, NIKE], not an
   arbitrary protocol that happens to implement the DCGKA procedure surface.
   This higher-order module type makes that construction dependency explicit:
   a theorem instantiation supplies one protocol functor and applies it to the
   exact NIKE and symmetric-encryption modules whose games occur in the bound.

   The body of the construction and Appendix B's reductions remain imported
   paper evidence.  This type-level binding does not claim those algorithms or
   reductions were machine checked; it prevents the public theorem boundary
   from accepting an unrelated free-standing protocol module. *)
module type BEEKEM_PAPER_CONSTRUCTION(
  N : BEEKEM_NIKE,
  S : BEEKEM_SYMMETRIC_ENCRYPTION
) = {
  proc init(
    id : beekem_user,
    group : beekem_group,
    kappa : int
  ) : beekem_member_state

  proc create(
    state : beekem_member_state,
    initial_members : beekem_user fset
  ) : beekem_protocol_result

  proc add(
    state : beekem_member_state,
    target : beekem_user
  ) : beekem_protocol_result

  proc remove_member(
    state : beekem_member_state,
    target : beekem_user
  ) : beekem_protocol_result

  proc update(
    state : beekem_member_state
  ) : beekem_protocol_result

  proc process(
    state : beekem_member_state,
    sender : beekem_user,
    control : beekem_generated_message,
    direct : beekem_direct_message option
  ) : beekem_process_result
}.
