import Leanux.Proofs.WG.AuthenticatedEffects.SendWorkSelection

/-! The native handshake-send worker suffix preserves the residual work queue.
The dequeue itself is handled separately by the ordered occurrence carrier. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.SendWorkCauses
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Std.Do

def afterTake (pid : PeerId) : WG.M Unit := do
  let p ← getPeer pid
  if !p.handshakePending then invariant "queued work without a pending flag"
  setPeer pid {p with handshakePending := (← getDev).sendWorkQueue.contains pid}
  _ ← hidden (.sectionStart .sendWorker)
  handshakeSendWorker pid
  _ ← hidden (.sectionStop .sendWorker)

theorem flushed_factor (pid : PeerId) : runFlushedSendWork pid =
    (do modifyDev fun d => {d with sendWorkQueue := d.sendWorkQueue.erase pid}; afterTake pid) := rfl

theorem afterTake_frame (pid : PeerId) : SameView Queues.WorkQueueFrames.view (afterTake pid) := by
  intro initial
  change Preserves (fun w => Queues.WorkQueueFrames.view w = initial) _
  unfold afterTake
  simp only [getDev,hidden,invariant]
  repeat' first
    | (rx_retention_head get
       exact hoare_consequence (hoare_get _) (fun _ h => h) (fun _ _ h => h.2))
    | (rx_retention_head handshakeSendWorker
       exact (Queues.RxCredits.SendWork.worker_workQueues pid).wp (fun s => s = initial))
    | work_queue_step initial

theorem flushed_queue (pid : PeerId) (w v : WGWorld) (a b : Ambient)
    (run : ((runFlushedSendWork pid).run w).run a = .ok (((),v),b)) :
    queue v = (queue w).erase pid := by
  rw [flushed_factor,MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨result,taken,afterAmbient,erased,tail⟩ := run
  cases result
  have native := native_erase pid w taken a afterAmbient erased
  have same := (ProjectedAction.iff_run_ambient _ _ _).mp (afterTake_frame pid)
    taken afterAmbient () v b tail
  have projected := congrArg (fun q => (q.map (fun x => x.2.1)).getD []) same
  have queueSame : queue v = queue taken := by
    simpa only [queue,Queues.WorkQueueFrames.view,Option.map_map,Function.comp_def] using projected
  exact queueSame.trans native

theorem flushed_transports (pid : PeerId) (w v : WGWorld) (a b : Ambient)
    (carrier : Carrier h tickets w) (selected : Selected tickets pid ticket rest)
    (run : ((runFlushedSendWork pid).run w).run a = .ok (((),v),b)) :
    ticket.Valid h ∧ Carrier h rest v :=
  carrier.dequeue selected (flushed_queue pid w v a b run)

end Leanux.Proofs.WG.AuthenticatedEffects.SendWorkCauses
