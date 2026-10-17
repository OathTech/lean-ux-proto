import Leanux.Proofs.WG.Progress.FlushQueueFrames

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000

namespace Leanux.Proofs.WG.Progress
open Leanux Leanux.WG Leanux.Proofs.WG.Noise TimerDiscipline Std.Do

/-- The actual send flush retains its complete normal-return domain, including
pending validation, both section reads, and a possibly final peer release. -/
theorem runFlushedSendWork_queues (pid : PeerId) (d : Device) :
    Ensures (runFlushedSendWork pid) (fun g => g.dev = some d)
      (fun _ g => flushQueueAt g = some (flushedSendQueues pid d)) := by
  let P : WGWorld → Prop := fun g => flushQueueAt g = some (flushedSendQueues pid d)
  have removeFrame : Ensures (modifyDev fun d => {d with sendWorkQueue := d.sendWorkQueue.erase pid})
      (fun g => g.dev = some d) (fun _ => P) := by
    intro g ambient result final after device run
    cases run
    simp [P, flushQueueAt, flushQueueKernel, device, workQueues, flushedSendQueues]
  have peerFrame : Ensures (getPeer pid) P (fun _ => P) := by
    intro g ambient result final after pre run
    exact ((ensures_iff _ _ _).mpr (getPeer_spec pid P) g ambient result final after pre run).1
  have devFrame : Ensures getDev P (fun _ => P) := by
    intro g ambient result final after pre run
    cases device : g.dev with
    | none => simp [P, flushQueueAt, flushQueueKernel, device] at pre
    | some current =>
      simp [getDev, device] at run
      rcases run with ⟨⟨rfl, rfl⟩, rfl⟩
      exact pre
  have setFrame (peer : Peer) : Ensures (setPeer pid peer) P (fun _ => P) := by
    intro g ambient result final after pre run
    cases run
    cases device : g.dev with
    | none => simp [P, flushQueueAt, flushQueueKernel, device] at pre
    | some current => simpa [P, flushQueueAt, flushQueueKernel, device, workQueues] using pre
  have hiddenFrame (site : HiddenSite) : Ensures (hidden site : WG.M (List UInt8)) P (fun _ => P) :=
    (ensures_iff _ _ _).mpr (hoare_liftAmbient_variant (AmbientM.hidden site) P)
  have pureFrame {α : Type} (value : α) : Ensures (pure value : WG.M α) P (fun _ => P) := by
    intro g ambient result final after pre run; cases run; exact pre
  unfold runFlushedSendWork
  refine ensures_bind _ _ removeFrame ?_
  intro ignored
  refine ensures_bind _ _ peerFrame ?_
  intro peer
  cases pending : peer.handshakePending with
  | false =>
    simp only [Bool.not_false, ite_true]
    intro g ambient result final after pre run
    cases run
  | true =>
    simp only [Bool.not_true, Bool.false_eq_true, ite_false]
    refine ensures_bind _ _ devFrame ?_
    intro current
    refine ensures_bind _ _ (setFrame _) ?_
    intro ignored
    refine ensures_bind _ _ (hiddenFrame _) ?_
    intro ignored
    refine ensures_bind _ _ ((ensures_iff _ _ _).mpr
      (handshakeSendWorker_flushQueues pid (flushedSendQueues pid d))) ?_
    intro ignored
    exact ensures_bind _ _ (hiddenFrame _) (fun _ => pureFrame ())

/-- The actual clear flush erases the first matching clear occurrence on normal
return while retaining the send queue, including successful final release. -/
theorem runFlushedClearWork_queues (pid : PeerId) (d : Device) :
    Ensures (runFlushedClearWork pid) (fun g => g.dev = some d)
      (fun _ g => flushQueueAt g = some (flushedClearQueues pid d)) := by
  let P : WGWorld → Prop := fun g => flushQueueAt g = some (flushedClearQueues pid d)
  have removeFrame : Ensures (modifyDev fun d => {d with clearWorkQueue := d.clearWorkQueue.erase pid})
      (fun g => g.dev = some d) (fun _ => P) := by
    intro g ambient result final after device run
    cases run
    simp [P, flushQueueAt, flushQueueKernel, device, workQueues, flushedClearQueues]
  have hiddenFrame (site : HiddenSite) : Ensures (hidden site : WG.M (List UInt8)) P (fun _ => P) :=
    (ensures_iff _ _ _).mpr (hoare_liftAmbient_variant (AmbientM.hidden site) P)
  unfold runFlushedClearWork
  refine ensures_bind _ _ removeFrame ?_
  intro ignored
  refine ensures_bind _ _ (hiddenFrame _) ?_
  intro ignored
  refine ensures_bind _ _ ((ensures_iff _ _ _).mpr
    (queuedExpiredZeroKeyMaterial_flushQueues pid (flushedClearQueues pid d))) ?_
  intro ignored
  refine ensures_bind _ _ (hiddenFrame _) ?_
  intro ignored g ambient result final after pre run
  cases run
  exact pre

end Leanux.Proofs.WG.Progress
