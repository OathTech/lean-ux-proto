import Leanux.Proofs.WG.HandshakeSecurity.TimestampArchiveTimers

namespace Leanux.Proofs.WG.HandshakeSecurity.TimestampArchive
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes Queues Origins

theorem saved_store (pid : PeerId) (p : Peer) (a : WG.M α) (same : SameWGStore a)
    (history : List TimestampReceipt) :
    Framing.Preserves (fun w => StateInv history w ∧ Responder.SavedNativePeer pid p w) a := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w b x v c hi run
  have device : v.dev = w.dev :=
    congrArg WGStoreView.dev ((ProjectedAction.iff_run_ambient _ _ _).mp same w b x v c run)
  obtain ⟨d,hd,hp⟩ := hi.2
  exact ⟨(hoare_iff_run_ambient _ _ _).mp (frame_store history _ same)
    _ _ _ _ _ hi.1 run,d,device.trans hd,hp⟩

theorem send_dequeue (pid : PeerId) (history : List TimestampReceipt) :
    Framing.Preserves (StateInv history) (Responder.sendDequeue pid) := by
  unfold Responder.sendDequeue
  apply hoare_bind _ _ (modify_device (fun d => {d with sendWorkQueue := d.sendWorkQueue.erase pid})
    (fun _ => rfl) history)
  intro _
  apply hoare_bind _ _ (read_saved pid history)
  intro p
  have tail : Hoare (do
      let d ← getDev
      setPeer pid {p with handshakePending := d.sendWorkQueue.contains pid})
      (fun w => StateInv history w ∧ Responder.SavedNativePeer pid p w)
      (fun _ => StateInv history) := by
    apply hoare_bind _ _ (saved_store pid p getDev getDev_sameWGStore history)
    intro d
    exact write_saved pid p (fun p => {p with handshakePending := d.sendWorkQueue.contains pid})
      (fun _ => ⟨rfl,rfl⟩) history
  split
  · exact hoare_bind _ _ (hoare_liftAmbient (AmbientM.invariant _) _) (fun _ => tail)
  · exact tail

theorem flushed_send (pid : PeerId) (history : List TimestampReceipt) :
    Framing.Preserves (StateInv history) (runFlushedSendWork pid) := by
  rw [Responder.flushedSend_factor]
  exact preserves_bind (send_dequeue pid history) (fun _ =>
    preserves_bind (hoare_liftAmbient (AmbientM.hidden (.sectionStart .sendWorker)) _) (fun _ =>
      preserves_bind (send_worker pid history) (fun _ =>
        preserves_bind (hoare_liftAmbient (AmbientM.hidden (.sectionStop .sendWorker)) _)
          (fun _ => preserves_pure _))))

theorem flushed_clear (pid : PeerId) (history : List TimestampReceipt) :
    Framing.Preserves (StateInv history) (runFlushedClearWork pid) := by
  unfold runFlushedClearWork
  simp (config := {zeta := false}) only [hidden]
  repeat' first
    | (rx_retention_head queuedExpiredZeroKeyMaterial; exact clear_worker _ history)
    | archive_timer_actor_step history

end Leanux.Proofs.WG.HandshakeSecurity.TimestampArchive
