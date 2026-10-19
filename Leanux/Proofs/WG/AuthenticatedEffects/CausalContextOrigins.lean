import Leanux.Proofs.WG.AuthenticatedEffects.CausalScopeOrigin
import Leanux.Proofs.WG.AuthenticatedEffects.CausalStackInitialized
import Leanux.Proofs.WG.AuthenticatedEffects.CausalReceiptInitialized
import Leanux.Proofs.WG.AuthenticatedEffects.CausalSelectionInitialized

/-! A recorded current context points to its own earlier scope in the same
initialized execution. Delayed contexts inherit an exact earlier native effect;
this is the decreasing occurrence relation needed for causal-root induction.
The presence and authorization of a context are not assumed implicitly. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.ContextOrigins
open Leanux Leanux.WG Leanux.Proofs.Logged TransmitSecurity

theorem current_entry (history : List Event) (token : CausalScope.Token Cause)
    (current : CausalScope.current scope? history = .ok (some token)) :
    ∃ before after, history = before ++ Event.scope (.entered token) :: after := by
  obtain ⟨before,event,after,position,decoded⟩ := CausalScope.current_origin scope? history token current
  cases event with
  | scope event =>
    have equal : event = .entered token := Option.some.inj decoded
    subst event
    exact ⟨before,after,position⟩
  | old value => cases decoded
  | armed value => cases decoded
  | queued value => cases decoded
  | exchange value => cases decoded
  | keepalivePrepared pid run => cases decoded
  | protocolSocket receipt => cases decoded
  | cookieSocket receipt => cases decoded

theorem current_stack (trace : Runner.Trace) (placeholders : Bool)
    (history suffix : List Event) (index : Nat) (entry : GroOccurrence.Entry)
    (position : (runPrefixOuter (execute trace placeholders) []).2 = history ++ suffix)
    (current : CausalScope.current scope? history = .ok (some ⟨index,.stackInput entry⟩)) :
    ∃ before after,
      history = before ++ Event.scope (.entered ⟨index,.stackInput entry⟩) :: after ∧
      GroOccurrence.Accepted StackOrigins.candidate StackOrigins.replay entry before := by
  obtain ⟨before,after,entered⟩ := current_entry history _ current
  refine ⟨before,after,entered,?_⟩
  apply StackOrigins.initialized trace placeholders before (.scope (.entered ⟨index,.stackInput entry⟩))
    (after ++ suffix) _ entry rfl
  simp only [position,entered,List.append_assoc,List.cons_append]

theorem current_timer (trace : Runner.Trace) (placeholders : Bool)
    (history suffix : List Event) (index : Nat) (bound : UInt64) (pid : PeerId)
    (timer : PeerTimer) (entry : WheelEntry)
    (position : (runPrefixOuter (execute trace placeholders) []).2 = history ++ suffix)
    (current : CausalScope.current scope? history = .ok (some ⟨index,.timer bound pid timer entry⟩)) :
    ∃ before after,
      history = before ++ Event.scope (.entered ⟨index,.timer bound pid timer entry⟩) :: after ∧
      Selections.TimerEntry before bound pid timer entry := by
  obtain ⟨before,after,entered⟩ := current_entry history _ current
  refine ⟨before,after,entered,?_⟩
  apply Selections.initialized_timer_scope trace placeholders before (after ++ suffix) index bound pid timer entry
  simp only [position,entered,List.append_assoc,List.cons_append]

theorem current_work (trace : Runner.Trace) (placeholders : Bool)
    (history suffix : List Event) (index : Nat) (pid : PeerId) (entry : CausalSources.SendEntry)
    (position : (runPrefixOuter (execute trace placeholders) []).2 = history ++ suffix)
    (current : CausalScope.current scope? history = .ok (some ⟨index,.sendWork pid entry⟩)) :
    ∃ before after,
      history = before ++ Event.scope (.entered ⟨index,.sendWork pid entry⟩) :: after ∧
      Selections.WorkOrigin before pid entry := by
  obtain ⟨before,after,entered⟩ := current_entry history _ current
  refine ⟨before,after,entered,?_⟩
  apply Selections.initialized_work trace placeholders before (after ++ suffix) index pid entry
  simp only [position,entered,List.append_assoc,List.cons_append]

end Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.ContextOrigins
