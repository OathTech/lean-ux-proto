import Leanux.Proofs.WG.TimerDiscipline.HookObservationClaims
import Leanux.Proofs.WG.TimerDiscipline.ObservationBridge
import Leanux.Proofs.WG.TimerDiscipline.JitterBoundClaims
import Leanux.Proofs.WG.TimerDiscipline.JitterOutcomeClaims

/-! Current selected wheel-unit contracts. The outer nextDue branch and complete runTimers loop are separate obligations. -/

set_option autoImplicit false

namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG Leanux.Env Noise Std.Do

/-- Full Product observation of an already selected unit, retaining exact prefix and final snapshots. This corrects the obsolete logical-due conclusion. -/
theorem projected_timer_dispatch_due (worker : Worker) (pid : PeerId) (timer : PeerTimer)
    (we : WheelEntry) (step : Option UInt64) (d : Device) :
    Campaign2.Product.Ensures (observed (timerDispatchUnit_variant worker pid timer we step)
      (timerExecutionPath worker pid timer we step))
      (fun s => s.wg.device = some d)
      (fun result final => ∃ selected,
        result.1 = .ok ((pid, timer, selected), final) ∧
        worker.timer? = some timer ∧ selected.wg.device = some d) := by
  apply observed_effect
  intro initial result final device run
  cases result
  obtain ⟨selected, selection, callback, kind, same⟩ :=
    source_timer_dispatch_due worker pid timer we step initial final d device run
  refine ⟨Campaign2.Product.snapshot selected, ?_, kind, same⟩
  apply observe_ok
  simp only [timerExecutionPath, StateT.run_bind, selection]
  change ((fireWheelSelected worker pid timer we).run selected >>= fun out =>
    Except.ok ((pid, timer, Campaign2.Product.snapshot selected), out.2)) = _
  rw [callback]
  rfl

/-- Conditional retry effect from the actual selected-unit prefix observation, preserving the original full Product payload. -/
theorem projected_retransmit_dispatch (pid : PeerId) (we : WheelEntry) (step : Option UInt64)
    (identity attempts : Nat) (timer : Option UInt64) :
    Campaign2.Product.Ensures (observed
      (timerDispatchUnit_variant .timerRetransmit pid .retransmitHandshake we step)
      (do timerDispatchPrefix_variant .timerRetransmit pid .retransmitHandshake we step
          pure (pid, PeerTimer.retransmitHandshake)))
      (fun s => retryObservation s.toSnapshot pid = some (identity, attempts, timer))
      (fun result final => ∀ selected,
        result.1 = .ok ((pid, .retransmitHandshake), selected) →
        retryObservation final.toSnapshot pid = some (identity, nextAttempts attempts, none)) := by
  apply observed_effect
  intro initial result final pre run selected selection
  cases hp : (timerDispatchPrefix_variant .timerRetransmit pid .retransmitHandshake we step).run initial with
  | error stop =>
    change Campaign2.Product.observeResult
      ((timerDispatchPrefix_variant .timerRetransmit pid .retransmitHandshake we step).run initial >>=
        fun out => Except.ok ((pid, PeerTimer.retransmitHandshake), out.2)) = _ at selection
    rw [hp] at selection
    cases selection
  | ok pair =>
    obtain ⟨ignored, middle⟩ := pair
    cases ignored
    exact source_retransmit_dispatch pid we step identity attempts timer initial result final
      ⟨pre, middle, hp⟩ run

end Leanux.Proofs.WG.TimerDiscipline
