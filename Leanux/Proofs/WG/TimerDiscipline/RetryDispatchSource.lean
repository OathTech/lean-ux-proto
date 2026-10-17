import Leanux.Proofs.WG.TimerDiscipline.RetrySelectedSource
import Leanux.Proofs.WG.TimerDiscipline.RetryInspectionClaims
import Leanux.Proofs.WG.TimerDiscipline.RetryGiveUpFrames
import Leanux.Proofs.WG.TimerDiscipline.RetryEligibilitySource
import Leanux.Proofs.WG.TimerDiscipline.RetryDispatchLeaves
import Leanux.Proofs.WG.TimerDiscipline.RetryDispatchModel
import Leanux.Proofs.WG.TimerDiscipline.RetryDispatchFrames
import Leanux.Proofs.WG.TimerDiscipline.SendDispatchClaims
import Leanux.Proofs.WG.TimerDiscipline.SendDispatchWorkSource
import Leanux.Proofs.WG.TimerDiscipline.FireSelectionSource
import Leanux.Proofs.WG.Config.QuietTimers

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000

namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Leanux.Proofs.WG.Config Std.Do

/-- The original pair, without a scheduler inserted between its two calls. -/
def retryDispatch (horizon : UInt64) : M Unit := do
  Env.fireTimer .timerRetransmit horizon
  Env.runOneSendWorker

/-- Each copied observation begins at that original call's actual entry. -/
def observedRetryDispatch (horizon : UInt64) : M RetryDispatchObservation := do
  let timer ← observed (Env.fireTimer .timerRetransmit horizon)
    (timerExecutionPath .timerRetransmit horizon)
  let afterTimer ← Campaign2.read
  let send ← observed Env.runOneSendWorker sendWorkerExecution
  return ⟨timer.1, afterTimer, send.1⟩

theorem observedRetryDispatch_run (horizon : UInt64) (w : World) :
    (observedRetryDispatch horizon).run w =
      ((Env.fireTimer .timerRetransmit horizon).run w >>= fun timerOut =>
        Env.runOneSendWorker.run timerOut.2 >>= fun sendOut =>
          Except.ok (RetryDispatchObservation.mk
            (Campaign2.observeResult ((timerExecutionPath .timerRetransmit horizon).run w))
            (Campaign2.snapshot timerOut.2)
            (Campaign2.observeResult (sendWorkerExecution.run timerOut.2)), sendOut.2)) := by
  simp only [observedRetryDispatch, observed, StateT.run_bind, StateT.run_pure]
  dsimp only [Campaign2.inspect, Campaign2.read, StateT.run, Bind.bind, Except.bind, Pure.pure]
  cases ht : Env.fireTimer .timerRetransmit horizon w with
  | error e => rfl
  | ok pair =>
    obtain ⟨u, after⟩ := pair
    dsimp only [Except.pure]
    cases hs : Env.runOneSendWorker after <;> rfl

/-- Removing both observations preserves the exact original pair, including errors. -/
theorem observedRetryDispatch_erase (horizon : UInt64) :
    (do let _ ← observedRetryDispatch horizon; pure ()) = retryDispatch horizon := by
  funext w
  change StateT.run _ w = StateT.run _ w
  rw [StateT.run_bind, observedRetryDispatch_run]
  simp only [retryDispatch, StateT.run_bind, StateT.run_pure]
  cases ht : (Env.fireTimer .timerRetransmit horizon).run w with
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
