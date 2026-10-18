import Leanux.Proofs.WG.Noise.PendingTicketWorkerFrames
import Leanux.Proofs.WG.Noise.PendingTicketClearFrames
import Leanux.Proofs.WG.Index.FlushSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Noise.PendingTickets
open Leanux Leanux.WG Lifetimes Leanux.Proofs.Framing Std.Do

/-- The dequeue keeps the exact peer read paired with its flag write. An
arbitrary replacement peer would not preserve its pending allocation stamp. -/
theorem flushedSendPrepare_frame (pid : PeerId) : SameView view (Index.flushedSendPrepare pid) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w ambient result v after run
  cases device : w.dev with
  | none =>
    simp [Index.flushedSendPrepare,modifyDev,getPeer,getDev,device,invariant,AmbientM.invariant] at run
    cases run
  | some d =>
    cases peer : d.peers[pid]? with
    | none =>
      simp [Index.flushedSendPrepare,modifyDev,getPeer,getDev,device,peer,invariant,AmbientM.invariant] at run
      cases run
    | some p =>
      cases pendingFlag : p.handshakePending with
      | false =>
        simp [Index.flushedSendPrepare,modifyDev,getPeer,getDev,device,peer,pendingFlag,invariant,AmbientM.invariant] at run
        cases run
      | true =>
        simp [Index.flushedSendPrepare,modifyDev,getPeer,getDev,device,peer,pendingFlag,setPeer] at run
        obtain ⟨⟨rfl,rfl⟩,rfl⟩ := run
        apply Store.ext
        · rfl
        · funext tracked
          by_cases same : pid = tracked
          · subst tracked
            simp [view,pending,device,peer]
          · simp [view,pending,device,Std.TreeMap.getElem?_insert,same]

theorem retained_preserves {α : Type} {action : WG.M α}
    (retains : RetainsCall action) (entry : Store PeerId) :
    Ensures action (fun w => Retained entry (view w)) (fun _ w => Retained entry (view w)) :=
  (ensures_iff _ _ _).mpr (retains.wp (Retained entry)
    (fun _ _ later earlier => earlier.trans later))

theorem retains_of_preserves {α : Type} {action : WG.M α}
    (preserves : ∀ entry, Ensures action (fun w => Retained entry (view w))
      (fun _ w => Retained entry (view w))) : RetainsCall action := by
  intro entry
  apply hoare_consequence ((ensures_iff _ _ _).mp (preserves entry))
  · intro w same
    rw [same]
    exact Retained.refl _
  · exact fun _ _ hi => hi

theorem runFlushedSendWork_retained (pid : PeerId) : RetainsCall (runFlushedSendWork pid) := by
  apply retains_of_preserves
  intro entry
  exact Index.runFlushedSendWork_preserves _ pid
    (retained_preserves (retained_of_frame (flushedSendPrepare_frame pid)) entry)
    (retained_preserves (handshakeSendWorker_retained pid) entry)

theorem runFlushedClearWork_retained (pid : PeerId) : RetainsCall (runFlushedClearWork pid) := by
  apply retains_of_preserves
  intro entry
  exact Index.runFlushedClearWork_preserves _ pid
    (retained_preserves (retained_of_frame
      (modifyDev_frame (fun d => {d with clearWorkQueue := d.clearWorkQueue.erase pid})
        (fun _ => rfl) (fun _ => rfl))) entry)
    (retained_preserves (queuedExpiredZeroKeyMaterial_retained pid) entry)

/-- Every original bounded drain order, including the selected clear-work
early return, retains pending tickets. Its recorded Stops are unchanged. -/
theorem drainHandshakeSendWq_retained (upTo : Option PeerId) : RetainsCall (drainHandshakeSendWq upTo) := by
  apply retains_of_preserves
  intro entry
  exact Index.drainHandshakeSendWq_preserves _
    (fun pid => retained_preserves (runFlushedSendWork_retained pid) entry)
    (fun pid => retained_preserves (runFlushedClearWork_retained pid) entry) upTo

theorem timersStop_retained (pid : PeerId) : RetainsCall (timersStop pid) := by
  apply retains_of_preserves
  intro entry
  exact Index.timersStop_preserves _
    (fun pid timer => retained_preserves (retained_of_frame (delTimer_frame pid timer)) entry)
    (fun upTo => retained_preserves (drainHandshakeSendWq_retained upTo) entry) pid

theorem peerRemoveAfterDead_retained (pid : PeerId) : RetainsCall (peerRemoveAfterDead pid) := by
  apply retains_of_preserves
  intro entry
  exact Index.peerRemoveAfterDead_preserves _
    (fun pid => retained_preserves (keypairsClear_retained pid) entry)
    (fun pid => retained_preserves (timersStop_retained pid) entry)
    (fun upTo => retained_preserves (drainHandshakeSendWq_retained upTo) entry)
    (retained_preserves (retained_of_frame
      (modifyDev_frame (fun d => {d with numPeers := d.numPeers-1}) (fun _ => rfl) (fun _ => rfl))) entry)
    (fun pid => retained_preserves (peerPut_retained (some pid)) entry) pid

end Leanux.Proofs.WG.Noise.PendingTickets
