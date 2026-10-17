import Leanux.Proofs.WG.TimerDiscipline.SendDispatchSource
import Leanux.Proofs.WG.TimerDiscipline.WorkStateFrames

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000

namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

/-- The actual selected worker preserves its post-dequeue queue and pending flag
through both section reads and its retained reference release. Pending status
is membership in the residual queue; duplicate peer entries remain allowed. -/
theorem sendWorkerExecution_workView (d : Device) (units : List (Nat × Nat × Nat))
    (retained : RetainedSendQueue d) :
    Campaign2.Product.Ensures sendWorkerExecution
      (fun s => s.wg.device = some d ∧ s.ambient.unitPeers = units)
      (fun execution final => workObservation final.toSnapshot execution.pid =
        (some (d.sendWorkQueue.erase execution.pid), some ((d.sendWorkQueue.erase execution.pid).contains execution.pid))) := by
  intro w execution final pre run
  change (sendWorkerSelection.run w >>= fun sel =>
    (sendWorkerDequeue sel.1.2).run sel.2 >>= fun deq =>
    (hidden (.sectionStart .sendWorker) : Leanux.M (List UInt8)).run deq.2 >>= fun start =>
    (liftWG (handshakeSendWorker sel.1.2)).run start.2 >>= fun body =>
    (hidden (.sectionStop .sendWorker) : Leanux.M (List UInt8)).run body.2 >>= fun stop =>
    Except.ok (SendWorkerExecution.mk sel.1.1 sel.1.2 (Campaign2.Product.snapshot deq.2)
      start.1 (Campaign2.Product.snapshot start.2) (Campaign2.Product.snapshot body.2) stop.1, stop.2)) =
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
      cases hb : (hidden (.sectionStart .sendWorker) : Leanux.M (List UInt8)).run beforeSection with
      | error e => simp only [hb] at run; cases run
      | ok pair =>
        obtain ⟨bytes, afterStart⟩ := pair
        simp only [hb] at run
        cases hw : (liftWG (handshakeSendWorker selected.2)).run afterStart with
        | error e => simp only [hw] at run; cases run
        | ok pair =>
          obtain ⟨u, afterBody⟩ := pair
          simp only [hw] at run
          cases he : (hidden (.sectionStop .sendWorker) : Leanux.M (List UInt8)).run afterBody with
          | error e => simp only [he] at run; cases run
          | ok pair =>
            obtain ⟨stopBytes, afterStop⟩ := pair
            simp only [he] at run
            obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj run)
            have selection := sendWorkerSelection_effect d units w selected afterSelection pre hs
            obtain ⟨p, resident, pending, deq⟩ :=
              sendWorkerDequeue_effect selected.2 d afterSelection _ beforeSection selection.1 hd
            have ambientFrame {α : Type} (action : AmbientM α) (P : WGWorld → Prop) :
                Product.Ensures (liftAmbient action) (fun w => P w.wg) (fun _ w => P w.wg) := by
              intro initial value finish property actionRun
              change (action.run initial.ambient >>= fun (a, ambient) =>
                Except.ok (a, {initial with ambient})) = .ok (value, finish) at actionRun
              cases h : action.run initial.ambient with
              | error stop => rw [h] at actionRun; cases actionRun
              | ok pair => rw [h] at actionRun; cases actionRun; exact property
            have start := ambientFrame (AmbientM.hidden (.sectionStart .sendWorker))
              (fun g => g.dev = some (dequeuedSendDevice d selected.2 p))
              beforeSection bytes afterStart deq hb
            have workerPre : workerAt afterStart.wg selected.2 =
                some (p.internalId, p.timerHandshakeAttempts, p.refcount) := by
              simp [workerAt, peerAt, start, dequeuedSendDevice, workerView]
            have workPre : workAt afterStart.wg selected.2 =
                (some (d.sendWorkQueue.erase selected.2),
                 some ((d.sendWorkQueue.erase selected.2).contains selected.2)) := by
              simp [workAt, workKernel, start, dequeuedSendDevice]
            have body : workAt afterBody.wg selected.2 =
                (some (d.sendWorkQueue.erase selected.2),
                 some ((d.sendWorkQueue.erase selected.2).contains selected.2)) := by
              change (((handshakeSendWorker selected.2).run afterStart.wg).run afterStart.ambient >>=
                fun ((value, g), ambient) => Except.ok (value, {afterStart with wg := g, ambient})) = _ at hw
              cases actual : ((handshakeSendWorker selected.2).run afterStart.wg).run afterStart.ambient with
              | error stop => rw [actual] at hw; cases hw
              | ok pair =>
                obtain ⟨⟨value, g⟩, ambient⟩ := pair
                rw [actual] at hw
                cases hw
                exact handshakeSendWorker_workView selected.2 p.internalId
                  p.timerHandshakeAttempts p.refcount (d.sendWorkQueue.erase selected.2)
                  ((d.sendWorkQueue.erase selected.2).contains selected.2)
                  (retained selected.2 selection.2.2.1 p resident)
                  afterStart.wg afterStart.ambient u g ambient ⟨workerPre, workPre⟩ actual
            exact ambientFrame (AmbientM.hidden (.sectionStop .sendWorker))
              (fun g => workAt g selected.2 =
                (some (d.sendWorkQueue.erase selected.2),
                 some ((d.sendWorkQueue.erase selected.2).contains selected.2)))
              afterBody stopBytes afterStop body he

end Leanux.Proofs.WG.TimerDiscipline
