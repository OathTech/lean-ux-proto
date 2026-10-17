import Leanux.Proofs.WG.TimerDiscipline.SendRearmSource
import Leanux.Proofs.WG.TimerDiscipline.RetryRearmModel
import Leanux.Proofs.WG.TimerDiscipline.RetryDispatchClaims

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000
namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Campaign2.Product Std.Do

def observedRetryRearm (unit : RetryUnit) : Leanux.M RetryRearmObservation := do
  let inspection ← Campaign2.Product.inspect (retryInspectionPath unit)
  let timer ← observed (timerDispatchUnit_variant .timerRetransmit unit.pid .retransmitHandshake unit.wheel unit.step)
    (timerExecutionPath .timerRetransmit unit.pid .retransmitHandshake unit.wheel unit.step)
  let afterTimer ← Campaign2.Product.read
  let send ← observed Env.runOneSendWorker sendRearmExecution
  return ⟨timer.1, afterTimer, inspection, send.1⟩

theorem observedRetryRearm_run (unit : RetryUnit) (w : World) :
    (observedRetryRearm unit).run w =
      ((timerDispatchUnit_variant .timerRetransmit unit.pid .retransmitHandshake unit.wheel unit.step).run w >>= fun timerOut =>
        Env.runOneSendWorker.run timerOut.2 >>= fun sendOut =>
          Except.ok (RetryRearmObservation.mk
            (observeResult ((timerExecutionPath .timerRetransmit unit.pid .retransmitHandshake unit.wheel unit.step).run w))
            (snapshot timerOut.2) (observeResult ((retryInspectionPath unit).run w))
            (observeResult (sendRearmExecution.run timerOut.2)), sendOut.2)) := by
  simp only [observedRetryRearm, observed, StateT.run_bind, StateT.run_pure]
  dsimp only [Campaign2.Product.inspect, Campaign2.Product.read, StateT.run, Bind.bind, Except.bind, Pure.pure]
  cases ht : timerDispatchUnit_variant .timerRetransmit unit.pid .retransmitHandshake unit.wheel unit.step w with
  | error e => rfl
  | ok pair =>
    obtain ⟨u, after⟩ := pair
    dsimp only [Except.pure]
    cases hs : Env.runOneSendWorker after <;> rfl

theorem observedRetryRearm_project (unit : RetryUnit) :
    (do let result ← observedRetryRearm unit; pure result.dispatch) =
      observedRetryDispatch unit := by
  funext w
  change (do let result ← observedRetryRearm unit; pure result.dispatch).run w =
    (observedRetryDispatch unit).run w
  rw [observedRetryDispatch_run, StateT.run_bind, observedRetryRearm_run]
  cases ht : (timerDispatchUnit_variant .timerRetransmit unit.pid .retransmitHandshake unit.wheel unit.step).run w with
  | error e => rfl
  | ok pair =>
    obtain ⟨u, after⟩ := pair
    dsimp only [Bind.bind, Except.bind, Pure.pure]
    cases hs : Env.runOneSendWorker.run after with
    | error e => rfl
    | ok pair =>
      obtain ⟨u, final⟩ := pair
      change Except.ok ((RetryRearmObservation.mk _ _ _ _).dispatch, final) = _
      simp only [RetryRearmObservation.dispatch, sendRearmObservation_project]

theorem observedRetryRearm_erase (unit : RetryUnit) :
    (do let _ ← observedRetryRearm unit; pure ()) = retryDispatch unit := by
  rw [← observedRetryDispatch_erase, ← observedRetryRearm_project]
  simp only [bind_assoc, pure_bind]

end Leanux.Proofs.WG.TimerDiscipline
