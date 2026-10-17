import Leanux.Proofs.WG.TimerDiscipline.SendRearmSource
import Leanux.Proofs.WG.TimerDiscipline.RetryRearmFrames
import Leanux.Proofs.WG.TimerDiscipline.RetryDispatchClaims

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000
namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Campaign2 Std.Do

def observedRetryRearm (horizon : UInt64) : M RetryRearmObservation := do
  let timer ← observed (Env.fireTimer .timerRetransmit horizon)
    (timerExecutionPath .timerRetransmit horizon)
  let afterTimer ← Campaign2.read
  let send ← observed Env.runOneSendWorker sendRearmExecution
  return ⟨timer.1, afterTimer, send.1⟩

theorem observedRetryRearm_run (horizon : UInt64) (w : World) :
    (observedRetryRearm horizon).run w =
      ((Env.fireTimer .timerRetransmit horizon).run w >>= fun timerOut =>
        Env.runOneSendWorker.run timerOut.2 >>= fun sendOut =>
          Except.ok (RetryRearmObservation.mk
            (observeResult ((timerExecutionPath .timerRetransmit horizon).run w))
            (snapshot timerOut.2) (observeResult (sendRearmExecution.run timerOut.2)), sendOut.2)) := by
  simp only [observedRetryRearm, observed, StateT.run_bind, StateT.run_pure]
  dsimp only [Campaign2.inspect, Campaign2.read, StateT.run, Bind.bind, Except.bind, Pure.pure]
  cases ht : Env.fireTimer .timerRetransmit horizon w with
  | error e => rfl
  | ok pair =>
    obtain ⟨u, after⟩ := pair
    dsimp only [Except.pure]
    cases hs : Env.runOneSendWorker after <;> rfl

theorem observedRetryRearm_project (horizon : UInt64) :
    (do let result ← observedRetryRearm horizon; pure result.dispatch) =
      observedRetryDispatch horizon := by
  funext w
  change (do let result ← observedRetryRearm horizon; pure result.dispatch).run w =
    (observedRetryDispatch horizon).run w
  rw [observedRetryDispatch_run, StateT.run_bind, observedRetryRearm_run]
  cases ht : (Env.fireTimer .timerRetransmit horizon).run w with
  | error e => rfl
  | ok pair =>
    obtain ⟨u, after⟩ := pair
    dsimp only [Bind.bind, Except.bind, Pure.pure]
    cases hs : Env.runOneSendWorker.run after with
    | error e => rfl
    | ok pair =>
      obtain ⟨u, final⟩ := pair
      change Except.ok ((RetryRearmObservation.mk _ _ _).dispatch, final) = _
      simp only [RetryRearmObservation.dispatch, sendRearmObservation_project]

theorem observedRetryRearm_erase (horizon : UInt64) :
    (do let _ ← observedRetryRearm horizon; pure ()) = retryDispatch horizon := by
  rw [← observedRetryDispatch_erase, ← observedRetryRearm_project]
  simp only [bind_assoc, pure_bind]

end Leanux.Proofs.WG.TimerDiscipline
