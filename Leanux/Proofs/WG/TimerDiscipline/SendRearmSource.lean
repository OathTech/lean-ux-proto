import Leanux.Proofs.WG.TimerDiscipline.SendRearmModel
import Leanux.Proofs.WG.TimerDiscipline.SendDispatchSource
import Leanux.Proofs.WG.TimerDiscipline.ObservationPathsSource
import Leanux.Proofs.WG.TimerDiscipline.DataDoneSource
import Leanux.Proofs.WG.TimerDiscipline.InitiationArmSource

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000
namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG Noise Campaign2.Product Std.Do

def initiationRearmExecution (pid : PeerId) : M InitiationRearmExecution := do
  let observation ← observed (liftWG (sendHandshakeInitiation pid))
    (prefixInspect (liftWG (initiationArmPrefix pid))
      (clockJitterPath .timerJiffiesHandshakeInitiated .retransmitJitter))
  let beforeRelease ← Campaign2.Product.read
  return ⟨observation.1, beforeRelease⟩

def rearmWorkerBody (pid : PeerId) : M InitiationRearmExecution := do
  let arm ← initiationRearmExecution pid
  liftWG (peerPut (some pid))
  return arm

def sendRearmExecution : M SendRearmExecution := do
  let selected ← sendWorkerSelection
  sendWorkerDequeue selected.2
  let beforeSection ← Campaign2.Product.read
  let startBytes ← hidden (.sectionStart .sendWorker)
  let afterStart ← Campaign2.Product.read
  let arm ← rearmWorkerBody selected.2
  let afterBody ← Campaign2.Product.read
  let stopBytes ← hidden (.sectionStop .sendWorker)
  return ⟨⟨selected.1, selected.2, beforeSection, startBytes, afterStart, afterBody, stopBytes⟩, arm⟩

theorem rearm_read_ignore {α : Type} (next : M α) :
    (do let _ ← Campaign2.Product.read; next) = next := rfl

/-- The same original send runs; the extra reads never change the state. -/
theorem initiationRearmExecution_erase (pid : PeerId) :
    (do let _ ← initiationRearmExecution pid; pure ()) = liftWG (sendHandshakeInitiation pid) := by
  rw [← observed_erase (liftWG (sendHandshakeInitiation pid))
    (prefixInspect (liftWG (initiationArmPrefix pid))
      (clockJitterPath .timerJiffiesHandshakeInitiated .retransmitJitter))]
  simp only [initiationRearmExecution, bind_assoc, pure_bind, rearm_read_ignore]

theorem initiationRearmExecution_run (pid : PeerId) (w : World) :
    (initiationRearmExecution pid).run w =
      ((liftWG (sendHandshakeInitiation pid)).run w >>= fun out =>
        Except.ok (InitiationRearmExecution.mk
          (observeResult ((prefixInspect (liftWG (initiationArmPrefix pid))
            (clockJitterPath .timerJiffiesHandshakeInitiated .retransmitJitter)).run w))
          (snapshot out.2), out.2)) := by
  simp only [initiationRearmExecution, observed, StateT.run_bind, StateT.run_pure]
  dsimp only [Campaign2.Product.inspect, Campaign2.Product.read, StateT.run, Bind.bind, Except.bind, Pure.pure]
  cases h : (liftWG (sendHandshakeInitiation pid)) w <;> rfl

theorem rearmWorkerBody_erase (pid : PeerId) :
    (do let _ ← rearmWorkerBody pid; pure ()) = liftWG (handshakeSendWorker pid) := by
  rw [handshakeSendWorker, liftWG_bind_variant, ← initiationRearmExecution_erase pid]
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
  rw [show (liftM (handshakeSendWorker selected.2) : Leanux.M Unit) =
    liftWG (handshakeSendWorker selected.2) from rfl]
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

end Leanux.Proofs.WG.TimerDiscipline
