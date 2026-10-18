import Leanux.Proofs.WG.HandshakeSecurity.ResponderMaintenance

namespace Leanux.Proofs.WG.HandshakeSecurity.Responder
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do
open Lifetimes Queues Origins Origins.Retaining

def sendDequeue (pid : PeerId) : WG.M Unit := do
  modifyDev fun d => {d with sendWorkQueue := d.sendWorkQueue.erase pid}
  let p ← getPeer pid
  if !p.handshakePending then invariant "queued work without a pending flag"
  setPeer pid {p with handshakePending := (← getDev).sendWorkQueue.contains pid}

theorem flushedSend_factor (pid : PeerId) : runFlushedSendWork pid = (do
    sendDequeue pid
    _ ← hidden (.sectionStart .sendWorker)
    handshakeSendWorker pid
    _ ← hidden (.sectionStop .sendWorker)) := by
  have bind_congr {α β : Type} (a : WG.M α) (f g : α → WG.M β)
      (h : ∀ x, f x = g x) : (a >>= f) = (a >>= g) := congrArg (fun k => a >>= k) (funext h)
  simp only [runFlushedSendWork, sendDequeue, bind_assoc]
  apply bind_congr
  intro _
  apply bind_congr
  intro p
  by_cases h : (!p.handshakePending) = true
  all_goals simp only [h, Bool.false_eq_true, ite_true, ite_false, bind_assoc]

theorem sendDequeue_native (pid : PeerId) (confirmed : List Nat) :
    Preserves (History.Native confirmed) (sendDequeue pid) := by
  apply native_fields
  · apply pool_of_material
    intro initial
    unfold sendDequeue
    material_lower
    repeat' traffic_basic (fun p => p = initial)
  · intro initial
    unfold sendDequeue
    change Preserves (fun w => CurrentSlots.fields w = initial) _
    simp (config := {zeta := false}) only [invariant]
    repeat' slot_fields_step initial

theorem flushedSend_native (pid : PeerId) (confirmed : List Nat) :
    Preserves (History.Native confirmed) (runFlushedSendWork pid) := by
  rw [flushedSend_factor]
  exact preserves_bind (sendDequeue_native pid confirmed) (fun _ =>
    preserves_bind (hoare_liftAmbient (AmbientM.hidden (.sectionStart .sendWorker)) _) (fun _ =>
      preserves_bind (sendWorker_native pid confirmed) (fun _ =>
        preserves_bind (hoare_liftAmbient (AmbientM.hidden (.sectionStop .sendWorker)) _)
          (fun _ => preserves_pure _))))

theorem flushedClear_native (H1 : H1ResponderCurrentEdges) (pid : PeerId) (confirmed : List Nat) :
    Preserves (History.Native confirmed) (runFlushedClearWork pid) := by
  unfold runFlushedClearWork
  simp (config := {zeta := false}) only [hidden]
  repeat' first
    | (rx_retention_head queuedExpiredZeroKeyMaterial; exact clearWorker_native H1 _ confirmed)
    | responder_handshake_step confirmed

theorem drain_native (H1 : H1ResponderCurrentEdges) (upTo : Option PeerId) (confirmed : List Nat) :
    Preserves (History.Native confirmed) (drainHandshakeSendWq upTo) := by
  unfold drainHandshakeSendWq
  simp (config := {zeta := false}) only [Std.Legacy.Range.forIn_eq_forIn_range', peekUnit, resolveUnit, getAmbient, invariant]
  repeat' first
    | (rx_retention_head runFlushedSendWork; exact flushedSend_native _ confirmed)
    | (rx_retention_head runFlushedClearWork; exact flushedClear_native H1 _ confirmed)
    | (rx_retention_head ForIn.forIn
       apply list_view_spec id (History.Native confirmed)
       intro x b
       change Preserves (History.Native confirmed) _)
    | (first | rx_retention_head throw | rx_retention_head MonadExceptOf.throw
       apply (hoare_iff_run_ambient _ _ _).mpr
       intro w a result v b entry run
       cases run)
    | responder_handshake_step confirmed

theorem stopTimers_native (H1 : H1ResponderCurrentEdges) (pid : PeerId) (confirmed : List Nat) :
    Preserves (History.Native confirmed) (timersStop pid) := by
  unfold timersStop
  repeat' first
    | (rx_retention_head delTimer; exact delTimer_native _ _ confirmed)
    | (rx_retention_head drainHandshakeSendWq; exact drain_native H1 _ confirmed)
    | (rx_retention_head ForIn.forIn
       apply list_view_spec id (History.Native confirmed)
       intro x b
       change Preserves (History.Native confirmed) _)
    | responder_handshake_step confirmed

end Leanux.Proofs.WG.HandshakeSecurity.Responder
