import Leanux.Proofs.WG.TimerDiscipline.OuterFirstTurnModel
import Leanux.Proofs.WG.TimerDiscipline.OuterFirstTurnSource
import Leanux.Proofs.WG.TimerDiscipline.ObservationBridge

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG Leanux.Env

/-- Original remaining fuel, the actual selected-unit prefix observation,
and the exact suffix outcome from the actual post-unit state. -/
abbrev FirstTimerReceipt := Nat × (PeerId × PeerTimer × Campaign2.Product.Snapshot) ×
  Campaign2.Product.Outcome Bool

/-- Inspect the first unit and its original continuation, on actual states.
The final state of this probe is the immediate post-unit state; inspecting
the continuation does not replace that state by its later outcome. -/
def firstTimerReceiptPath (jPass : UInt64) (worker : Worker)
    (pid : PeerId) (timer : PeerTimer) (we : WheelEntry) : Leanux.M FirstTimerReceipt := do
  modifyWG fun g => {g with queuedThisCall := []}
  let budget ← recordBudget
  let selection ← timerExecutionPath worker pid timer we none
  let suffix ← Campaign2.Product.inspect (firstTimerContinuation jPass (budget - 1) we)
  pure (budget - 1, selection, suffix)

/-- Whole-call normal return derives the actual prefix, unit and suffix
successes. No successful callback or prefix is assumed at entry. -/
theorem runTimers_first_receipt_run (jPass : UInt64) (worker : Worker)
    (pid : PeerId) (timer : PeerTimer) (we : WheelEntry)
    (initial final : World) (result : Bool)
    (selection : FirstTimerSelected jPass worker pid timer we (Campaign2.Product.snapshot initial))
    (run : (Env.runTimers jPass).run initial = .ok (result, final)) :
    let start : World := {initial with wg := {initial.wg with queuedThisCall := []}}
    ∃ remaining selected afterUnit,
      (recordBudget : Leanux.M Nat).run start = .ok (remaining + 1, start) ∧
      (timerDispatchPrefix_variant worker pid timer we none).run start = .ok ((), selected) ∧
      (timerDispatchUnit_variant worker pid timer we none).run start = .ok ((), afterUnit) ∧
      (fireWheelSelected worker pid timer we).run selected = .ok ((), afterUnit) ∧
      (firstTimerContinuation jPass remaining we).run afterUnit = .ok (result, final) ∧
      worker.timer? = some timer ∧ selected.wg.dev = initial.wg.dev ∧
      (firstTimerReceiptPath jPass worker pid timer we).run initial =
        .ok ((remaining, (pid, timer, Campaign2.Product.snapshot selected),
          .ok (result, Campaign2.Product.snapshot final)), afterUnit) := by
  obtain ⟨d, site, device, nextSite, sectionMatch, notClear, wheel⟩ := selection
  let start : World := {initial with wg := {initial.wg with queuedThisCall := []}}
  let remaining : Nat := match initial.ambient.hidden with
    | some records => records.length
    | none => DOMAIN_FILTER_TURNS - 1
  have budget : (recordBudget : Leanux.M Nat).run start = .ok (remaining + 1, start) := by
    change Except.ok ((match initial.ambient.hidden with
      | some rs => rs.length + 1
      | none => DOMAIN_FILTER_TURNS), start) = _
    dsimp only [remaining]
    cases initial.ambient.hidden <;> rfl
  rw [runTimers_first_timer_run jPass worker pid timer we initial d site
    device nextSite sectionMatch notClear wheel] at run
  change ((do let budget ← recordBudget
              timerDispatchUnit_variant worker pid timer we none
              firstTimerContinuation jPass (budget - 1) we).run start) = _ at run
  rw [StateT.run_bind, budget] at run
  change ((timerDispatchUnit_variant worker pid timer we none).run start >>= fun out =>
    (firstTimerContinuation jPass remaining we).run out.2) = .ok (result, final) at run
  cases unitRun : (timerDispatchUnit_variant worker pid timer we none).run start with
  | error stop => rw [unitRun] at run; cases run
  | ok out =>
    obtain ⟨value, afterUnit⟩ := out
    cases value
    rw [unitRun] at run
    have suffix : (firstTimerContinuation jPass remaining we).run afterUnit = .ok (result, final) := run
    obtain ⟨selected, prefixRun, callback, kind, sameDevice⟩ :=
      fireTimer_execution worker pid timer we none start afterUnit d device unitRun
    have path : (timerExecutionPath worker pid timer we none).run start =
        .ok ((pid, timer, Campaign2.Product.snapshot selected), afterUnit) := by
      simp only [timerExecutionPath, StateT.run_bind, prefixRun]
      change ((fireWheelSelected worker pid timer we).run selected >>= fun out =>
        Except.ok ((pid, timer, Campaign2.Product.snapshot selected), out.2)) = _
      rw [callback]
      rfl
    refine ⟨remaining, selected, afterUnit, budget, prefixRun, unitRun, callback, suffix,
      kind, sameDevice.trans device.symm, ?_⟩
    change ((do let budget ← recordBudget
                let selection ← timerExecutionPath worker pid timer we none
                let suffix ← Campaign2.Product.inspect (firstTimerContinuation jPass (budget - 1) we)
                pure (budget - 1, selection, suffix)).run start) = _
    rw [StateT.run_bind, budget]
    change ((timerExecutionPath worker pid timer we none).run start >>= fun out =>
      Except.ok ((remaining, out.1,
        Campaign2.Product.observeResult ((firstTimerContinuation jPass remaining we).run out.2)), out.2)) = _
    rw [path]
    change Except.ok ((remaining, (pid, timer, Campaign2.Product.snapshot selected),
      Campaign2.Product.observeResult ((firstTimerContinuation jPass remaining we).run afterUnit)), afterUnit) = _
    rw [suffix]
    rfl

end Leanux.Proofs.WG.TimerDiscipline
