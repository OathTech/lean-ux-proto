import Leanux.Proofs.WG.TimerDiscipline.RetryInspectionClaims
import Leanux.Proofs.WG.TimerDiscipline.RetryDispatchLeaves
import Leanux.Proofs.WG.TimerDiscipline.RetryUnitModel
import Leanux.Proofs.WG.TimerDiscipline.RetrySelectedSource
import Leanux.Proofs.WG.TimerDiscipline.SectionFrames
import Leanux.Proofs.WG.TimerDiscipline.RetryInspectedSource
import Leanux.Proofs.WG.TimerDiscipline.ObservationBridge
import Leanux.Proofs.WG.TimerDiscipline.SelectionFrames

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000
namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Leanux.Proofs.WG.Config Std.Do

/-- Inspect the same actual selected-unit execution, retaining the queue bit. -/
def retryInspectionPath (unit : RetryUnit) : Leanux.M (Option Bool) := do
  timerDispatchPrefix_variant .timerRetransmit unit.pid .retransmitHandshake unit.wheel unit.step
  observedFireSelected unit.pid unit.wheel

def retryDispatch (unit : RetryUnit) : Leanux.M Unit := do
  timerDispatchUnit_variant .timerRetransmit unit.pid .retransmitHandshake unit.wheel unit.step
  Env.runOneSendWorker

def observedRetryDispatch (unit : RetryUnit) : Leanux.M RetryDispatchObservation := do
  let inspection ← Campaign2.Product.inspect (retryInspectionPath unit)
  let timer ← observed
    (timerDispatchUnit_variant .timerRetransmit unit.pid .retransmitHandshake unit.wheel unit.step)
    (timerExecutionPath .timerRetransmit unit.pid .retransmitHandshake unit.wheel unit.step)
  let afterTimer ← Campaign2.Product.read
  let send ← observed Env.runOneSendWorker sendWorkerExecution
  return ⟨timer.1, afterTimer, inspection, send.1⟩

theorem observedRetryDispatch_run (unit : RetryUnit) (w : World) :
    (observedRetryDispatch unit).run w =
      ((timerDispatchUnit_variant .timerRetransmit unit.pid .retransmitHandshake unit.wheel unit.step).run w >>= fun timerOut =>
        Env.runOneSendWorker.run timerOut.2 >>= fun sendOut =>
          Except.ok (RetryDispatchObservation.mk
            (Campaign2.Product.observeResult ((timerExecutionPath .timerRetransmit unit.pid .retransmitHandshake unit.wheel unit.step).run w))
            (Campaign2.Product.snapshot timerOut.2)
            (Campaign2.Product.observeResult ((retryInspectionPath unit).run w))
            (Campaign2.Product.observeResult (sendWorkerExecution.run timerOut.2)), sendOut.2)) := by
  simp only [observedRetryDispatch, observed, StateT.run_bind, StateT.run_pure]
  dsimp only [Campaign2.Product.inspect, Campaign2.Product.read, StateT.run, Bind.bind, Except.bind, Pure.pure]
  cases ht : timerDispatchUnit_variant .timerRetransmit unit.pid .retransmitHandshake unit.wheel unit.step w with
  | error e => rfl
  | ok pair =>
    obtain ⟨u, after⟩ := pair
    dsimp only [Except.pure]
    cases hs : Env.runOneSendWorker after <;> rfl

theorem observedRetryDispatch_erase (unit : RetryUnit) :
    (do let _ ← observedRetryDispatch unit; pure ()) = retryDispatch unit := by
  funext w
  change StateT.run _ w = StateT.run _ w
  rw [StateT.run_bind, observedRetryDispatch_run]
  simp only [StateT.run_bind, StateT.run_pure]
  cases ht : (timerDispatchUnit_variant .timerRetransmit unit.pid .retransmitHandshake unit.wheel unit.step).run w with
  | error e => rfl
  | ok pair =>
    obtain ⟨u, after⟩ := pair
    dsimp only [Bind.bind, Except.bind, Pure.pure]
    cases hs : Env.runOneSendWorker.run after with
    | error e => rfl
    | ok pair =>
      obtain ⟨u, final⟩ := pair
      cases u
      rfl


end Leanux.Proofs.WG.TimerDiscipline
