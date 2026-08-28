require import AllCore List FSet.
require import ProtocolTypes ProtocolChecks.

(* Mathematical causal-state representation used by Deliverable A4.  The
   executable protocol stores a finite node-id set and a closure function.
   The reference representation stores the same immutable node/context facts
   as a newest-first list.  A hash collision is handled separately by A1; this
   file proves the exact closure mapping once node identifiers are fixed. *)

type causal_record = {
  cr_node_id : node_id;
  cr_context : fact_id fset
}.

op causal_record_ids (records : causal_record list) : node_id fset =
  with records = [] => fset0
  with records = record :: rest =>
    fset1 record.`cr_node_id `|` causal_record_ids rest.

op causal_record_lookup
    (records : causal_record list)
    (candidate : node_id) : fact_id fset option =
  with records = [] => None
  with records = record :: rest =>
    if record.`cr_node_id = candidate
    then Some record.`cr_context
    else causal_record_lookup rest candidate.

pred protocol_state_represents_causal_records
    (state : protocol_state)
    (records : causal_record list) =
     state.`ps_nodes = causal_record_ids records
  /\ (forall candidate,
        state.`ps_closures candidate =
          causal_record_lookup records candidate).

op causal_records_exact_predecessor_closure
    (records : causal_record list)
    (predecessors : node_id fset) : fact_id fset option =
  closure_union_list
    (causal_record_lookup records)
    (elems predecessors).

lemma closure_union_list_pointwise
    (left right : closure_map)
    (predecessors : node_id list) :
  (forall node, left node = right node) =>
  closure_union_list left predecessors =
    closure_union_list right predecessors.
proof.
  elim: predecessors => [| predecessor rest ih] //=.
  move=> pointwise.
  rewrite (pointwise predecessor) (ih pointwise).
qed.

lemma represented_exact_predecessor_closure
    (state : protocol_state)
    (records : causal_record list)
    (predecessors : node_id fset) :
  protocol_state_represents_causal_records state records =>
  exact_predecessor_closure state predecessors =
    causal_records_exact_predecessor_closure records predecessors.
proof.
  move=> [_ closures].
  rewrite /exact_predecessor_closure
    /causal_records_exact_predecessor_closure.
  exact (closure_union_list_pointwise
    state.`ps_closures
    (causal_record_lookup records)
    (elems predecessors)
    closures).
qed.

lemma acceptance_preserves_causal_representation
    (state : protocol_state)
    (records : causal_record list)
    (envelope : operation_envelope)
    (node : node_id)
    (context : fact_id fset) :
  protocol_state_represents_causal_records state records =>
  protocol_state_represents_causal_records
    (protocol_state_after_acceptance state envelope node context)
    ({| cr_node_id = node; cr_context = context |} :: records).
proof.
  move=> [nodes closures].
  rewrite /protocol_state_represents_causal_records.
  split.
  + rewrite /protocol_state_after_acceptance /causal_record_ids /= nodes.
    by rewrite fsetUC.
  + move=> candidate.
    rewrite /protocol_state_after_acceptance /closure_map_insert
      /causal_record_lookup /=.
    case (candidate = node)=> [->|different].
    + by rewrite eq_refl.
    + have node_different : node <> candidate by smt().
      rewrite different node_different.
      exact (closures candidate).
qed.
