import Leanux.Proofs.WG.HandshakeSecurity.PeerReferenceTimers

/-! Native deferred actors return with positive resident counts. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.PeerReference
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues Origins

theorem saved_store (p : Peer) (a : WG.M α) (same : SameWGStore a) :
    Framing.Preserves (fun w => Inv w ∧ 0 < p.refcount) a := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w b x v c hi run
  exact ⟨(hoare_iff_run_ambient _ _ _).mp (store same) w b x v c hi.1 run,hi.2⟩

theorem send_dequeue (pid : PeerId) : Framing.Preserves Inv (Responder.sendDequeue pid) := by
  unfold Responder.sendDequeue
  apply hoare_bind _ _ (modify_device (fun d => {d with sendWorkQueue := d.sendWorkQueue.erase pid})
    (fun _ => rfl))
  intro _
  apply hoare_bind _ _ (read_saved pid)
  intro p
  have tail : Hoare (do
      let d ← getDev
      setPeer pid {p with handshakePending := d.sendWorkQueue.contains pid})
      (fun w => Inv w ∧ 0 < p.refcount) (fun _ => Inv) := by
    apply hoare_bind _ _ (saved_store p getDev getDev_sameWGStore)
    intro d
    exact write_saved pid p (fun p => {p with handshakePending := d.sendWorkQueue.contains pid})
      (fun _ => rfl)
  split
  · exact hoare_bind _ _ (hoare_liftAmbient (AmbientM.invariant _) _) (fun _ => tail)
  · exact tail

theorem flushed_send (pid : PeerId) : Framing.Preserves Inv (runFlushedSendWork pid) := by
  rw [Responder.flushedSend_factor]
  exact preserves_bind (send_dequeue pid) (fun _ =>
    preserves_bind (hoare_liftAmbient (AmbientM.hidden (.sectionStart .sendWorker)) _) (fun _ =>
      preserves_bind (send_worker pid) (fun _ =>
        preserves_bind (hoare_liftAmbient (AmbientM.hidden (.sectionStop .sendWorker)) _)
          (fun _ => preserves_pure _))))

theorem flushed_clear (pid : PeerId) : Framing.Preserves Inv (runFlushedClearWork pid) := by
  unfold runFlushedClearWork
  simp (config := {zeta := false}) only [hidden]
  repeat' first
    | (rx_retention_head queuedExpiredZeroKeyMaterial; exact clear_worker _)
    | peer_reference_timer_actor_step

end Leanux.Proofs.WG.HandshakeSecurity.PeerReference
