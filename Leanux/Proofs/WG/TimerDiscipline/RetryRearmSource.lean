import Leanux.Proofs.WG.TimerDiscipline.RetryRearmFrames
import Leanux.Proofs.WG.TimerDiscipline.RetryDispatchClaims

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000
namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Campaign2 Std.Do

def initiationRearmExecution (pid : PeerId) : M InitiationRearmExecution := do
  let observation ← observed (sendHandshakeInitiation pid)
    (prefixInspect (initiationArmPrefix pid)
      (clockJitterPath .timerJiffiesHandshakeInitiated .retransmitJitter))
  let beforeRelease ← Campaign2.read
  return ⟨observation.1, beforeRelease⟩

def rearmWorkerBody (pid : PeerId) : M InitiationRearmExecution := do
  let arm ← initiationRearmExecution pid
  peerPut (some pid)
  return arm

def sendRearmExecution : M SendRearmExecution := do
  let selected ← sendWorkerSelection
  sendWorkerDequeue selected.2
  let beforeSection ← Campaign2.read
  let startBytes ← hidden (.sectionStart .sendWorker)
  let afterStart ← Campaign2.read
  let arm ← rearmWorkerBody selected.2
  let afterBody ← Campaign2.read
  let stopBytes ← hidden (.sectionStop .sendWorker)
  return ⟨⟨selected.1, selected.2, beforeSection, startBytes, afterStart, afterBody, stopBytes⟩, arm⟩

def observedRetryRearm (horizon : UInt64) : M RetryRearmObservation := do
  let timer ← observed (Env.fireTimer .timerRetransmit horizon)
    (timerExecutionPath .timerRetransmit horizon)
  let afterTimer ← Campaign2.read
  let send ← observed Env.runOneSendWorker sendRearmExecution
  return ⟨timer.1, afterTimer, send.1⟩

theorem rearm_read_ignore {α : Type} (next : M α) :
    (do let _ ← Campaign2.read; next) = next := rfl

/-- The same original send runs; the extra reads never change the state. -/
theorem initiationRearmExecution_erase (pid : PeerId) :
    (do let _ ← initiationRearmExecution pid; pure ()) = sendHandshakeInitiation pid := by
  rw [← observed_erase (sendHandshakeInitiation pid)
    (prefixInspect (initiationArmPrefix pid)
      (clockJitterPath .timerJiffiesHandshakeInitiated .retransmitJitter))]
  simp only [initiationRearmExecution, bind_assoc, pure_bind, rearm_read_ignore]

theorem initiationRearmExecution_run (pid : PeerId) (w : World) :
    (initiationRearmExecution pid).run w =
      ((sendHandshakeInitiation pid).run w >>= fun out =>
        Except.ok (InitiationRearmExecution.mk
          (observeResult ((prefixInspect (initiationArmPrefix pid)
            (clockJitterPath .timerJiffiesHandshakeInitiated .retransmitJitter)).run w))
          (snapshot out.2), out.2)) := by
  simp only [initiationRearmExecution, observed, StateT.run_bind, StateT.run_pure]
  dsimp only [Campaign2.inspect, Campaign2.read, StateT.run, Bind.bind, Except.bind, Pure.pure]
  cases h : sendHandshakeInitiation pid w <;> rfl

theorem rearmWorkerBody_erase (pid : PeerId) :
    (do let _ ← rearmWorkerBody pid; pure ()) = handshakeSendWorker pid := by
  rw [handshakeSendWorker, ← initiationRearmExecution_erase pid]
  simp only [rearmWorkerBody, bind_assoc, pure_bind]
  simp

theorem sendRearmExecution_project :
    (do let result ← sendRearmExecution; pure result.send) = sendWorkerExecution := by
  simp only [sendRearmExecution, sendWorkerExecution, bind_assoc, pure_bind]
  congr 1
  funext selected
  congr 1
  funext u
  congr 1
  funext beforeSection
  congr 1
  funext startBytes
  congr 1
  funext afterStart
  rw [← rearmWorkerBody_erase selected.2]
  simp only [bind_assoc, pure_bind]

theorem sendRearmExecution_erase :
    (do let _ ← sendRearmExecution; pure ()) = Env.runOneSendWorker := by
  rw [← sendWorkerExecution_erase, ← sendRearmExecution_project]
  simp only [bind_assoc, pure_bind]

theorem sendRearmExecution_success (w final : World)
    (run : Env.runOneSendWorker.run w = .ok ((), final)) :
    ∃ execution, sendRearmExecution.run w = .ok (execution, final) := by
  have erased : (do let _ ← sendRearmExecution; pure () : M Unit).run w = .ok ((), final) := by
    rw [sendRearmExecution_erase]
    exact run
  change (sendRearmExecution.run w >>= fun out => Except.ok ((), out.2)) = .ok ((), final) at erased
  cases he : sendRearmExecution.run w with
  | error e => rw [he] at erased; cases erased
  | ok pair =>
    obtain ⟨execution, after⟩ := pair
    rw [he] at erased
    have eq := congrArg Prod.snd (Except.ok.inj erased)
    cases eq
    exact ⟨execution, rfl⟩

theorem sendRearmObservation_project (w : World) :
    (observeResult (sendRearmExecution.run w)).map (fun (send, final) => (send.send, final)) =
      observeResult (sendWorkerExecution.run w) := by
  rw [← sendRearmExecution_project]
  change _ = observeResult (sendRearmExecution.run w >>= fun out => Except.ok (out.1.send, out.2))
  cases h : sendRearmExecution.run w <;> rfl

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
