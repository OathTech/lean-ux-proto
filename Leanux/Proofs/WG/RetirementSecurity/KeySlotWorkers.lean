import Leanux.Proofs.WG.RetirementSecurity.KeySlotCombinedFrames
import Leanux.Proofs.WG.RetirementSecurity.KeySlotConsumers

/-! Native send/clear work and timer drains retain slot liveness even when
payments delete peers. Saved PENDING and timer writes retain the actual saved
record relation; the make-dead exception is not discharged by a work payment. -/
namespace Leanux.Proofs.WG.RetirementSecurity.KeySlotLiveness
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues Queues.RxCredits

theorem handshake_clear (pid : PeerId) : Preserves (InvExcept pending) (handshakeClear pid) :=
  combined_frame (ConfiguredMaintenance.handshakeClear_view pid) (ClearedSlots.handshake_clear_points pid)

theorem send_worker (pid : PeerId) : Preserves (InvExcept pending) (handshakeSendWorker pid) := by
  unfold handshakeSendWorker
  exact preserves_bind (initiation pid) (fun _=>peer_put (some pid))

theorem zero_worker (pid : PeerId) : Preserves (InvExcept pending) (queuedExpiredZeroKeyMaterial pid) := by
  unfold queuedExpiredZeroKeyMaterial
  exact preserves_bind (handshake_clear pid) (fun _=>preserves_bind (clear pid) (fun _=>peer_put (some pid)))

macro "key_slot_work_step" : tactic => `(tactic| first
  | key_slot_saved_step
  | (rx_retention_head get; exact hoare_consequence (hoare_get _) (fun _ h=>h) (fun _ _ h=>h.2))
  | (rx_retention_head handshakeSendWorker; exact send_worker _)
  | (rx_retention_head queuedExpiredZeroKeyMaterial; exact zero_worker _)
  | (rx_retention_head hidden; unfold hidden)
  | (rx_retention_head delTimer; exact del_timer _ _)
  | (rx_retention_head modifyDev; apply modify; intro d; rfl)
  | key_slot_step)

theorem flushed_send (pid : PeerId) : Preserves (InvExcept pending) (runFlushedSendWork pid) := by
  unfold runFlushedSendWork
  repeat' key_slot_work_step

theorem flushed_clear (pid : PeerId) : Preserves (InvExcept pending) (runFlushedClearWork pid) := by
  unfold runFlushedClearWork
  repeat' key_slot_work_step

theorem drain (upTo : Option PeerId) : Preserves (InvExcept pending) (drainHandshakeSendWq upTo) :=
  HolderDrain.drain_rule upTo _
    (fun w v _ pid a b before _ _ run=>
      (hoare_iff_run_ambient _ _ _).mp (flushed_send pid) w a () v b before run)
    (fun w v _ pid a b before _ _ run=>
      (hoare_iff_run_ambient _ _ _).mp (flushed_clear pid) w a () v b before run)

theorem timers_stop (pid : PeerId) : Preserves (InvExcept pending) (timersStop pid) := by
  unfold timersStop
  apply preserves_bind
  · apply list_view_spec id (InvExcept pending)
    intro timer u
    exact preserves_bind (del_timer pid timer) (fun _=>preserves_pure _)
  · intro _
    apply preserves_bind (store getDev_sameWGStore)
    intro d
    split
    · exact drain _
    · exact preserves_pure ()

theorem reset (pid : PeerId) : Preserves (InvExcept pending) (resetLastSentHandshake pid) := by
  unfold resetLastSentHandshake
  simp only [hiddenClock64]
  repeat' key_slot_work_step

end Leanux.Proofs.WG.RetirementSecurity.KeySlotLiveness
