import Leanux.Proofs.WG.TimerDiscipline.SendDispatchSource
import Leanux.Proofs.WG.TimerDiscipline.WorkStateFrames

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000

namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

/-- The actual selected worker preserves its post-dequeue queue and pending flag
through both section reads and its retained reference release. -/
theorem sendWorkerExecution_workView (d : Device) (units : List (Nat × Nat × Nat))
    (retained : RetainedSendQueue d) :
    Campaign2.Ensures sendWorkerExecution
      (fun s => s.wg.device = some d ∧ s.ambient.unitPeers = units)
      (fun execution final => workObservation final execution.pid =
        (some (d.sendWorkQueue.erase execution.pid), some false)) := by
  intro w execution final pre run
  change (sendWorkerSelection.run w >>= fun sel =>
    (sendWorkerDequeue sel.1.2).run sel.2 >>= fun deq =>
    (hidden (.sectionStart .sendWorker)).run deq.2 >>= fun start =>
    (handshakeSendWorker sel.1.2).run start.2 >>= fun body =>
    (hidden (.sectionStop .sendWorker)).run body.2 >>= fun stop =>
    Except.ok (SendWorkerExecution.mk sel.1.1 sel.1.2 (Campaign2.snapshot deq.2)
      start.1 (Campaign2.snapshot start.2) (Campaign2.snapshot body.2) stop.1, stop.2)) =
      .ok (execution, final) at run
  cases hs : sendWorkerSelection.run w with
  | error e => simp only [hs, Bind.bind, Except.bind] at run; cases run
  | ok pair =>
    obtain ⟨selected, afterSelection⟩ := pair
    simp only [hs, Bind.bind, Except.bind] at run
    cases hd : (sendWorkerDequeue selected.2).run afterSelection with
    | error e => simp only [hd] at run; cases run
    | ok pair =>
      obtain ⟨u, beforeSection⟩ := pair
      simp only [hd] at run
      cases hb : (hidden (.sectionStart .sendWorker)).run beforeSection with
      | error e => simp only [hb] at run; cases run
      | ok pair =>
        obtain ⟨bytes, afterStart⟩ := pair
        simp only [hb] at run
        cases hw : (handshakeSendWorker selected.2).run afterStart with
        | error e => simp only [hw] at run; cases run
        | ok pair =>
          obtain ⟨u, afterBody⟩ := pair
          simp only [hw] at run
          cases he : (hidden (.sectionStop .sendWorker)).run afterBody with
          | error e => simp only [he] at run; cases run
          | ok pair =>
            obtain ⟨stopBytes, afterStop⟩ := pair
            simp only [he] at run
            obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj run)
            have selection := sendWorkerSelection_effect d units w selected afterSelection pre hs
            obtain ⟨p, resident, pending, deq⟩ :=
              sendWorkerDequeue_effect selected.2 d afterSelection _ beforeSection selection.1 hd
            have start := (ensures_iff _ _ _).mpr
              (hidden_kernel_spec (fun k => k.wg = some (dequeuedSendDevice d selected.2 p))
                (.sectionStart .sendWorker)) beforeSection bytes afterStart deq hb
            have workerPre : workerAt afterStart selected.2 =
                some (p.internalId, p.timerHandshakeAttempts, p.refcount) := by
              simp [workerAt, peerAt, start, dequeuedSendDevice, workerView]
            have workPre : workAt afterStart selected.2 =
                (some (d.sendWorkQueue.erase selected.2), some false) := by
              simp [workAt, workKernel, start, dequeuedSendDevice]
            have body := handshakeSendWorker_workView selected.2 p.internalId
              p.timerHandshakeAttempts p.refcount (d.sendWorkQueue.erase selected.2) false
              (retained selected.2 selection.2.2.1 p resident)
              afterStart _ afterBody ⟨workerPre, workPre⟩ hw
            exact (ensures_iff _ _ _).mpr
              (hidden_kernel_spec
                (fun k => workKernel k selected.2 =
                  (some (d.sendWorkQueue.erase selected.2), some false))
                (.sectionStop .sendWorker)) afterBody stopBytes afterStop body he

end Leanux.Proofs.WG.TimerDiscipline
