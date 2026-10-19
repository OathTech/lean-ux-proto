import Leanux.Proofs.WG.AuthenticatedEffects.CausalSelectionSend

/-! A selected timer's lexical token is paired with the immediately preceding
native selection receipt. Actual nextDue and saved-device facts are caller
obligations; an arbitrary invocation of the observer is not a valid dispatch. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Selections
open Leanux Leanux.WG Leanux.Proofs.Logged TransmitSecurity

theorem timer_selected (d : Device) (bound : UInt64) (pid : PeerId)
    (timer : PeerTimer) (entry : WheelEntry) :
    PrefixEnsures (fun h w => Inv h w.wg ∧ w.wg.dev = some d ∧
      TimerWheel.nextDue d bound = some (pid,timer,entry)) Safe
      (hooks.timerSelected d bound pid timer entry)
      (fun _ h w => Inv h w.wg) := by
  intro w h input
  let receipt : TimerDispatch.Selection := ⟨d,bound,pid,timer,entry,w⟩
  have origin : TimerOrigin h receipt :=
    TimerOrigin.of_carrier h receipt ⟨input.2.1,input.2.2⟩ input.1.1.1
  have selected := input.1.2.emit (event := .old (.timerSelected receipt)) origin
  have scopeSafe := selected.emit
    (event := .scope (.entered ⟨(h ++ [Event.old (.timerSelected receipt)]).length,.timer bound pid timer entry⟩))
    (show TimerEntry (h ++ [Event.old (.timerSelected receipt)]) bound pid timer entry from
      ⟨h,receipt,rfl,rfl,rfl,rfl,rfl,origin⟩)
  let suffix := [Event.old (.timerSelected receipt),
    Event.scope (.entered ⟨(h ++ [Event.old (.timerSelected receipt)]).length,.timer bound pid timer entry⟩)]
  have same :
      runPrefix (hooks.timerSelected d bound pid timer entry) w h =
        (.ok ((h ++ [Event.old (.timerSelected receipt)]).length,w),h ++ suffix) := by
    change runPrefix (CausalSources.timerEnter Event.scope (fun r => .old (.timerSelected r)) d bound pid timer entry) w h = _
    rw [CausalSources.timerEnter,TimerDispatch.scope_run]
    change ((Except.ok ((h ++ [Event.old (.timerSelected receipt)]).length,w) : Except Stop (Nat × World)),
      (h ++ [Event.old (.timerSelected receipt)]) ++ [Event.scope (.entered ⟨(h ++ [Event.old (.timerSelected receipt)]).length,.timer bound pid timer entry⟩)]) = _
    simp only [List.append_assoc,List.singleton_append]
    rfl
  rw [same]
  have safe : Safe (h ++ suffix) := by
    simpa only [List.append_assoc,List.singleton_append] using scopeSafe
  exact ⟨suffix,rfl,safe,input.1.1.append suffix,safe⟩

theorem timer_finished (token : Nat) :
    PrefixPreserves (fun h w => Inv h w.wg) Safe (hooks.timerFinished token) := by
  intro w h input
  have safe := input.2.emit (event := .scope (.exited token)) True.intro
  exact ⟨[.scope (.exited token)],rfl,safe,input.1.append _,safe⟩

end Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Selections
