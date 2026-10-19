import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedTimerPointCoverage

/-! Selection emits the saved native tuple before entering its lexical
scope. These concrete points preserve the same explicit ledger and world. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Timer.Points
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity CausalJournal

theorem Native.accounted (token : Native) {value : token.Result}
    (before : CompleteCarrier.Accounted h ledger debts locals w.wg)
    (performed : runPrefix token.action w h = (.ok (value,v),last)) :
    CompleteCarrier.Accounted last ledger debts locals v.wg := by
  cases token with
  | world => cases performed; exact before
  | history => cases performed; exact before
  | selected receipt =>
    change ((Except.ok ((),w) : Except Stop (Unit × World)),h ++ [.old (.timerSelected receipt)]) = (.ok (value,v),last) at performed
    rcases Prod.mk.inj performed with ⟨same,rfl⟩
    cases same
    exact before.append_quiet _ (by intro event member; simp only [List.mem_singleton] at member; subst event; rfl)
      (by intro event member position; simp only [List.mem_singleton] at member; subst event; rfl)
  | scope event =>
    change ((Except.ok ((),w) : Except Stop (Unit × World)),h ++ [.scope event]) = (.ok (value,v),last) at performed
    rcases Prod.mk.inj performed with ⟨same,rfl⟩
    cases same
    exact before.append_quiet _ (by intro event member; simp only [List.mem_singleton] at member; subst event; rfl)
      (by intro event member position; simp only [List.mem_singleton] at member; subst event; rfl)

theorem selected_run (device : Device) (bound : UInt64) (pid : PeerId) (timer : PeerTimer) (entry : WheelEntry)
    (w : World) (h : History) :
    runPrefix (hooks.timerSelected device bound pid timer entry) w h =
      (.ok (h.length+1,w),h ++ [Event.old (.timerSelected ⟨device,bound,pid,timer,entry,w⟩),
        Event.scope (.entered ⟨h.length+1,.timer bound pid timer entry⟩)]) := by
  change (Except.ok ((h ++ [Event.old (.timerSelected ⟨device,bound,pid,timer,entry,w⟩)]).length,w),
    (h ++ [Event.old (.timerSelected ⟨device,bound,pid,timer,entry,w⟩)]) ++
      [Event.scope (.entered ⟨(h ++ [Event.old (.timerSelected ⟨device,bound,pid,timer,entry,w⟩)]).length,
        .timer bound pid timer entry⟩)]) = _
  simp only [List.length_append,List.length_singleton,List.append_assoc,List.singleton_append]

theorem selected_valid (device : w.wg.dev = some d)
    (due : TimerWheel.nextDue d bound = some (pid,timer,entry)) :
    TimerDispatch.Selection.Valid ⟨d,bound,pid,timer,entry,w⟩ := ⟨device,due⟩

theorem finished_run (token : Nat) (w : World) (h : History) :
    runPrefix (hooks.timerFinished token) w h = (.ok ((),w),h ++ [.scope (.exited token)]) := rfl
end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Timer.Points
