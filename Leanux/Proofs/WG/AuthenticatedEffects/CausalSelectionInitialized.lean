import Leanux.Proofs.WG.AuthenticatedEffects.CausalSelectionOuter

/-! Initialized delayed occurrence provenance on the final causal journal.
The earlier arm/enqueue receipt is native and positional; authorizing its own
lexical cause remains the independent causal-root obligation. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Selections
open Leanux Leanux.WG Leanux.Proofs.Logged TransmitSecurity

theorem initialized_timer (trace : Runner.Trace) (placeholders : Bool)
    (pre post : List Event) (receipt : TimerDispatch.Selection)
    (position : (runPrefixOuter (execute trace placeholders) []).2 =
      pre ++ Event.old (.timerSelected receipt) :: post) : TimerOrigin pre receipt :=
  (Carrier.initialized trace placeholders).timer position

theorem initialized_work (trace : Runner.Trace) (placeholders : Bool)
    (pre post : List Event) (index : Nat) (pid : PeerId) (entry : CausalSources.SendEntry)
    (position : (runPrefixOuter (execute trace placeholders) []).2 =
      pre ++ Event.scope (.entered ⟨index,.sendWork pid entry⟩) :: post) : WorkOrigin pre pid entry :=
  (Carrier.initialized trace placeholders).work position

theorem initialized_timer_scope (trace : Runner.Trace) (placeholders : Bool)
    (pre post : List Event) (index : Nat) (bound : UInt64) (pid : PeerId) (timer : PeerTimer) (entry : WheelEntry)
    (position : (runPrefixOuter (execute trace placeholders) []).2 =
      pre ++ Event.scope (.entered ⟨index,.timer bound pid timer entry⟩) :: post) :
    TimerEntry pre bound pid timer entry :=
  (Carrier.initialized trace placeholders).timer_entry position

theorem initialized_timer_arm (trace : Runner.Trace) (placeholders : Bool)
    (pre post : List Event) (receipt : TimerDispatch.Selection)
    (position : (runPrefixOuter (execute trace placeholders) []).2 =
      pre ++ Event.old (.timerSelected receipt) :: post) :
    receipt.Valid ∧ ∃ before after arm stamp expires,
      pre = before ++ Event.armed arm :: after ∧ arm.Valid ∧ TimerOccurrences.Changed arm ∧
      arm.peer = receipt.peer ∧ arm.timer = receipt.timer ∧
      TimerSlots.Pending arm.run.after receipt.peer receipt.timer stamp expires receipt.entry ∧
      TimerSlots.Pending receipt.before.wg receipt.peer receipt.timer stamp expires receipt.entry := by
  obtain ⟨valid,stamp,expires,pending,arm,recorded,peer,timer,armed⟩ := initialized_timer trace placeholders pre post receipt position
  obtain ⟨before,after,occurred,native,changed⟩ := recorded
  exact ⟨valid,before,after,arm,stamp,expires,occurred,native,changed,peer,timer,armed,pending⟩

end Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Selections
