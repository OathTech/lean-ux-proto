import Leanux.Proofs.WG.Progress.ScheduleTurn

set_option autoImplicit false
set_option pp.structureInstances false

namespace Leanux.Proofs.WG.Progress
open Leanux Leanux.WG Leanux.Env

def placeholderDispatch (worker : Worker) : M TurnResult := do
  if !(← dispatch worker) then invariant s!"{worker.symbol} has work but was not dispatched"
  return turnContinue

def placeholderTurn (d : Device) : M TurnResult := do
  let some worker := placeholderSelection d | return turnReturn
  placeholderDispatch worker

theorem turn_placeholder (stack : Option Worker) (initial : World) (d : Device)
    (records : initial.ambient.hidden = none) (device : initial.wg.dev = some d) :
    (scheduleTurn stack).run initial = (placeholderTurn d).run initial := by
  have hd : (monadLift getDev : Leanux.M Device).run initial = .ok (d, initial) := by
    have native : ((getDev.run initial.wg).run initial.ambient) =
        .ok ((d, initial.wg), initial.ambient) := by
      simp [getDev, device]
      rfl
    change (((getDev.run initial.wg).run initial.ambient) >>= fun ((value, wg), ambient) =>
      Except.ok (value, {initial with wg, ambient})) = _
    rw [native]
    rfl
  have hg (w : World) : (getAmbient : Leanux.M Ambient).run w = .ok (w.ambient, w) := rfl
  have hok {α β : Type} (x : α) (f : α → Except Stop β) :
      (Except.ok x >>= f) = f x := rfl
  simp only [scheduleTurn, scheduleTurnWith, StateT.run_bind, hg,
    records, Option.isNone_none, ite_true, hd, hok]
  rfl

theorem placeholder_none_iff (d : Device) : placeholderSelection d = none ↔
    d.handshakeQueue.empty = true ∧ d.decryptQueue.empty = true ∧
      d.encryptQueue.empty = true ∧ d.txWorkQueue.isEmpty = true := by
  cases h1 : d.handshakeQueue.empty <;> cases h2 : d.decryptQueue.empty <;>
    cases h3 : d.encryptQueue.empty <;> cases h4 : d.txWorkQueue.isEmpty <;>
    simp [placeholderSelection, h1, h2, h3, h4]

theorem turn_placeholder_empty (stack : Option Worker) (initial : World) (d : Device)
    (records : initial.ambient.hidden = none) (device : initial.wg.dev = some d)
    (empty : d.handshakeQueue.empty = true ∧ d.decryptQueue.empty = true ∧
      d.encryptQueue.empty = true ∧ d.txWorkQueue.isEmpty = true) :
    (scheduleTurn stack).run initial = .ok (turnReturn, initial) := by
  rw [turn_placeholder stack initial d records device]
  have selection := (placeholder_none_iff d).mpr empty
  simp only [placeholderTurn, selection]
  rfl

theorem placeholderDispatch_success_iff (worker : Worker) (initial final : World) :
    (placeholderDispatch worker).run initial = .ok (turnContinue, final) ↔
      DispatchRun worker initial final := by
  rw [← dispatch_success_iff]
  simp only [placeholderDispatch, StateT.run_bind]
  cases hd : (dispatch worker).run initial with
  | error err =>
    change (Except.error err = Except.ok (turnContinue, final)) ↔ (Except.error err = Except.ok (true, final))
    simp
  | ok pair =>
    obtain ⟨dispatched, afterDispatch⟩ := pair
    cases dispatched
    · change (Except.error (Stop.invariant _) = Except.ok (turnContinue, final)) ↔
        (Except.ok (false, afterDispatch) = Except.ok (true, final))
      simp
    · change (Except.ok (turnContinue, afterDispatch) = Except.ok (turnContinue, final)) ↔
        (Except.ok (true, afterDispatch) = Except.ok (true, final))
      simp

theorem turn_placeholder_dispatch (stack : Option Worker) (worker : Worker)
    (initial : World) (d : Device) (records : initial.ambient.hidden = none)
    (device : initial.wg.dev = some d) (selected : placeholderSelection d = some worker) :
    (scheduleTurn stack).run initial = (placeholderDispatch worker).run initial := by
  rw [turn_placeholder stack initial d records device]
  simp only [placeholderTurn, selected]

theorem placeholderDispatch_false (worker : Worker) (initial afterDispatch : World)
    (empty : (dispatch worker).run initial = .ok (false, afterDispatch)) :
    (placeholderDispatch worker).run initial =
      .error (.invariant s!"{worker.symbol} has work but was not dispatched") := by
  rw [placeholderDispatch, StateT.run_bind, empty]
  rfl

theorem placeholderDispatch_error (worker : Worker) (initial : World) (err : Stop)
    (failed : (dispatch worker).run initial = .error err) :
    (placeholderDispatch worker).run initial = .error err := by
  rw [placeholderDispatch, StateT.run_bind, failed]
  rfl

end Leanux.Proofs.WG.Progress
