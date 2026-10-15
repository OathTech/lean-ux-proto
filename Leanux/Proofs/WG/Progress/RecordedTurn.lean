import Leanux.Proofs.WG.Progress.ScheduleTurn

set_option autoImplicit false
set_option pp.structureInstances false

namespace Leanux.Proofs.WG.Progress
open Leanux Leanux.WG Leanux.Env Leanux.Proofs.WG.Config

theorem turn_dispatch (stack : Option Worker) (worker : Worker)
    (initial afterPeek : World) (next : Option Nat)
    (records : initial.hidden.isNone = false)
    (peek : peekHiddenSite.run initial = .ok (next, afterPeek))
    (start : next.bind sectionOf = some (worker, true)) :
    (scheduleTurn stack).run initial =
      ((dispatch worker).run afterPeek >>= fun out =>
        pure (if out.1 then turnContinue else turnReturn, out.2)) := by
  have hok {α β : Type} (x : α) (f : α → Except Stop β) :
      (Except.ok x >>= f) = f x := rfl
  simp only [scheduleTurn, StateT.run_bind, StateT.run_get, pure_bind,
    records, Bool.false_eq_true, ite_false, peek, hok, start]
  cases hd : (dispatch worker).run afterPeek with
  | error err => rfl
  | ok pair =>
    obtain ⟨dispatched, afterDispatch⟩ := pair
    cases dispatched <;> rfl

theorem turn_dispatch_continue_iff (stack : Option Worker) (worker : Worker)
    (initial afterPeek final : World) (next : Option Nat)
    (records : initial.hidden.isNone = false)
    (peek : peekHiddenSite.run initial = .ok (next, afterPeek))
    (start : next.bind sectionOf = some (worker, true)) :
    (scheduleTurn stack).run initial = .ok (turnContinue, final) ↔ DispatchRun worker afterPeek final := by
  rw [turn_dispatch stack worker initial afterPeek next records peek start,
    ← dispatch_success_iff]
  cases hd : (dispatch worker).run afterPeek with
  | error err =>
    change (Except.error err = Except.ok (turnContinue, final)) ↔
      (Except.error err = Except.ok (true, final))
    simp
  | ok pair =>
    obtain ⟨dispatched, afterDispatch⟩ := pair
    change (Except.ok ((if dispatched then turnContinue else turnReturn), afterDispatch) =
      Except.ok (turnContinue, final)) ↔ (Except.ok (dispatched, afterDispatch) = Except.ok (true, final))
    cases dispatched <;> simp [turnContinue, turnReturn]

theorem turn_dispatch_return_iff (stack : Option Worker) (worker : Worker)
    (initial afterPeek final : World) (next : Option Nat)
    (records : initial.hidden.isNone = false)
    (peek : peekHiddenSite.run initial = .ok (next, afterPeek))
    (start : next.bind sectionOf = some (worker, true)) :
    (scheduleTurn stack).run initial = .ok (turnReturn, final) ↔
      (dispatchPrefix worker).run afterPeek = .ok (none, final) := by
  rw [turn_dispatch stack worker initial afterPeek next records peek start,
    ← dispatch_false_iff]
  cases hd : (dispatch worker).run afterPeek with
  | error err =>
    change (Except.error err = Except.ok (turnReturn, final)) ↔
      (Except.error err = Except.ok (false, final))
    simp
  | ok pair =>
    obtain ⟨dispatched, afterDispatch⟩ := pair
    change (Except.ok ((if dispatched then turnContinue else turnReturn), afterDispatch) =
      Except.ok (turnReturn, final)) ↔ (Except.ok (dispatched, afterDispatch) = Except.ok (false, final))
    cases dispatched <;> simp [turnContinue, turnReturn]

theorem turn_dispatch_error (stack : Option Worker) (worker : Worker)
    (initial afterPeek : World) (next : Option Nat) (err : Stop)
    (records : initial.hidden.isNone = false)
    (peek : peekHiddenSite.run initial = .ok (next, afterPeek))
    (start : next.bind sectionOf = some (worker, true))
    (failed : (dispatch worker).run afterPeek = .error err) :
    (scheduleTurn stack).run initial = .error err := by
  rw [turn_dispatch stack worker initial afterPeek next records peek start, failed]
  rfl

/-- Original NAPI continuation, including its post-poll peek and early return. -/
def napiTurn : M TurnResult := do
  napiSoftirq
  if (← peekHiddenSite) == some (HiddenSite.sectionStart .netRx).info.id then return turnReturn
  return turnContinue

theorem turn_napi (stack : Option Worker) (initial afterPeek : World) (next : Option Nat)
    (d : Device) (records : initial.hidden.isNone = false)
    (peek : peekHiddenSite.run initial = .ok (next, afterPeek))
    (noStart : ∀ worker, next.bind sectionOf ≠ some (worker, true))
    (device : afterPeek.k.wg = some d)
    (poll : (next == some (HiddenSite.sectionStart .netRx).info.id &&
      d.peers.toList.any (·.2.napiScheduled)) = true) :
    (scheduleTurn stack).run initial = napiTurn.run afterPeek := by
  have hd : getDev.run afterPeek = .ok (d, afterPeek) := by
    simp [getDev, getK, StateT.run, bind, pure, get, getThe, MonadStateOf.get,
      StateT.bind, StateT.pure, StateT.get, Except.bind, Except.pure, device]
  have hok {α β : Type} (x : α) (f : α → Except Stop β) :
      (Except.ok x >>= f) = f x := rfl
  simp only [scheduleTurn, StateT.run_bind, StateT.run_get, pure_bind,
    records, Bool.false_eq_true, ite_false, peek, hok]
  cases hs : next.bind sectionOf with
  | none =>
    simp only [StateT.run_bind, hd, hok, poll, ite_true]
    rfl
  | some pair =>
    obtain ⟨worker, starts⟩ := pair
    cases starts with
    | true => exact False.elim (noStart worker hs)
    | false =>
      simp only [StateT.run_bind, hd, hok, poll, ite_true]
      rfl

theorem napiTurn_execution (initial final : World) (result : TurnResult)
    (run : napiTurn.run initial = .ok (result, final)) :
    ∃ afterPoll next,
      napiSoftirq.run initial = .ok ((), afterPoll) ∧
      peekHiddenSite.run afterPoll = .ok (next, final) ∧
      result = if next == some (HiddenSite.sectionStart .netRx).info.id then turnReturn else turnContinue := by
  have hok {α β : Type} (x : α) (f : α → Except Stop β) :
      (Except.ok x >>= f) = f x := rfl
  simp only [napiTurn, StateT.run_bind] at run
  cases hp : napiSoftirq.run initial with
  | error err => rw [hp] at run; cases run
  | ok pair =>
    obtain ⟨u, afterPoll⟩ := pair
    cases u
    rw [hp] at run
    simp only [hok] at run
    cases hn : peekHiddenSite.run afterPoll with
    | error err => rw [hn] at run; cases run
    | ok pair =>
      obtain ⟨next, afterPeek⟩ := pair
      rw [hn] at run
      simp only [hok] at run
      split at run <;> rename_i selected
      all_goals
        simp only [StateT.run_pure, Except.ok.injEq, Prod.mk.injEq] at run
        obtain ⟨value, same⟩ := run
        exact ⟨afterPoll, next, rfl, hn, by simp [selected]⟩

end Leanux.Proofs.WG.Progress
