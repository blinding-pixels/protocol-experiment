import Std

namespace CausalDagCgka

/--
The live DCGKA state and retrospective-history state are separate products.
This is an operational separation theorem, not a computational-security proof.
-/
structure CompositeState (Live History : Type) where
  live : Live
  history : History

/-- Events are domain-separated at the state-machine level. -/
inductive CompositeEvent (LiveEvent HistoryEvent : Type)
  | live : LiveEvent → CompositeEvent LiveEvent HistoryEvent
  | history : HistoryEvent → CompositeEvent LiveEvent HistoryEvent

/-- One product-state transition. -/
def compositeStep {Live History LiveEvent HistoryEvent : Type}
    (liveStep : Live → LiveEvent → Live)
    (historyStep : History → HistoryEvent → History)
    (state : CompositeState Live History) :
    CompositeEvent LiveEvent HistoryEvent → CompositeState Live History
  | .live event =>
      { live := liveStep state.live event, history := state.history }
  | .history event =>
      { live := state.live, history := historyStep state.history event }

/-- A history-only event cannot mutate the live BeeKEM/DCGKA state. -/
@[simp] theorem history_step_preserves_live
    {Live History LiveEvent HistoryEvent : Type}
    (liveStep : Live → LiveEvent → Live)
    (historyStep : History → HistoryEvent → History)
    (state : CompositeState Live History) (event : HistoryEvent) :
    (compositeStep liveStep historyStep state (.history event)).live = state.live := by
  rfl

/-- A live event cannot mutate retrospective-history state. -/
@[simp] theorem live_step_preserves_history
    {Live History LiveEvent HistoryEvent : Type}
    (liveStep : Live → LiveEvent → Live)
    (historyStep : History → HistoryEvent → History)
    (state : CompositeState Live History) (event : LiveEvent) :
    (compositeStep liveStep historyStep state (.live event)).history = state.history := by
  rfl

/-- Independent live and history transitions commute exactly. -/
theorem live_history_steps_commute
    {Live History LiveEvent HistoryEvent : Type}
    (liveStep : Live → LiveEvent → Live)
    (historyStep : History → HistoryEvent → History)
    (state : CompositeState Live History)
    (liveEvent : LiveEvent) (historyEvent : HistoryEvent) :
    compositeStep liveStep historyStep
        (compositeStep liveStep historyStep state (.live liveEvent))
        (.history historyEvent)
      =
    compositeStep liveStep historyStep
        (compositeStep liveStep historyStep state (.history historyEvent))
        (.live liveEvent) := by
  rfl

/-- Run only history transitions. -/
def runHistory {Live History HistoryEvent : Type}
    (historyStep : History → HistoryEvent → History) :
    CompositeState Live History → List HistoryEvent → CompositeState Live History
  | state, [] => state
  | state, event :: rest =>
      runHistory historyStep
        { live := state.live, history := historyStep state.history event }
        rest

/-- Any finite history-only execution preserves the entire live state. -/
theorem runHistory_preserves_live
    {Live History HistoryEvent : Type}
    (historyStep : History → HistoryEvent → History)
    (state : CompositeState Live History) (events : List HistoryEvent) :
    (runHistory historyStep state events).live = state.live := by
  induction events generalizing state with
  | nil => rfl
  | cons event rest ih =>
      have h := ih
        ({ live := state.live,
           history := historyStep state.history event } : CompositeState Live History)
      simpa [runHistory] using h

end CausalDagCgka
