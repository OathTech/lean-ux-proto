import Leanux.Proofs.WG.HandshakeSecurity.ReceiveMaterialStack
import Leanux.Proofs.WG.HandshakeSecurity.ReceiveMaterialWorkerFrames

/-! Actual crypt, transmit and decrypt iterations carry RX allocation
certificates through softirq and rescheduling on the same shared journal. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.ReceiveMaterial.Execution
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes Queues AuthenticatedEffects Responder TransmitSecurity

theorem poll : ProductSafe Journal.poll :=
  product_observed
    (history_receipt_product _ _ (fun _ => ⟨rfl,by intro p k receipt impossible; cases impossible⟩)
      (history_focus_product _ _ (fun _ => ⟨rfl,by intro p k receipt impossible; cases impossible⟩) _))
    (TransportJournal.product_erases Journal.handshake? Journal.HandshakeProjection.poll)
    (fun _ => PublicationPoll.native_product _ _ bounded_encrypt_poll)

theorem encrypt (item : Option (List SkbId)) : ProductSafe (Journal.encrypt item) :=
  product_observed
    (history_receipt_product _ _ (fun _ => ⟨rfl,by intro p k receipt impossible; cases impossible⟩)
      (history_focus_product _ _ (fun _ => ⟨rfl,by intro p k receipt impossible; cases impossible⟩) _))
    (TransportJournal.product_erases Journal.handshake? (Journal.HandshakeProjection.encrypt item))
    (fun _ => bounded_encrypt_tail item)

theorem tx_step (pid : PeerId) : ProductSafe (Journal.transmit pid) :=
  product_observed
    (history_focus_product Journal.completionEvent Journal.completion?
      (fun event => by
        cases event <;> exact ⟨rfl,by intro p k receipt impossible; cases impossible⟩) _)
    (TransportJournal.product_erases Journal.handshake? (Journal.HandshakeProjection.transmit pid))
    (fun _ => PublicationPoll.native_product _ _ (bounded_transmit pid))

theorem product_ambient (action : AmbientM α) :
    ProductSafe (liftPrefix (monadLift action : Leanux.M α)) :=
  product_lift _ (fun _ => productAmbient_spec action _ (fun _ _ hi => hi))

theorem resched (worker : Worker) (site : Decision) : ProductSafe (Driver.reschedObserved worker site) :=
  product_bind (product_store _ (condResched_sameKernel worker)) (fun _ => product_ambient _)

theorem encrypt_tail (item : Option (List SkbId)) :
    ProductSafe (Driver.encryptTailObserved Journal.hooks item) :=
  workerIterPrefix_preserves _ _ (fun _ _ hi => hi.2) (encrypt item) (resched _ _)

theorem encrypt_iteration : ProductSafe (Driver.encryptIterObserved Journal.hooks) :=
  product_bind poll (fun _ => product_bind softirq (fun _ => encrypt_tail _))

theorem tx_iteration (pid : PeerId) : ProductSafe (Driver.txIterObserved Journal.hooks pid) :=
  workerIterPrefix_preserves _ _ (fun _ _ hi => hi.2) (tx_step pid) (resched _ _)

theorem decrypt_step : ProductSafe (Driver.decryptStepObserved Journal.hooks) := by
  unfold Driver.decryptStepObserved RxWorkers.decryptWith
  apply product_bind softirq
  intro _
  apply product_bind prepare
  intro peer
  cases peer with
  | none => exact product_pure _
  | some pid =>
    exact product_bind irq_exit (fun _ =>
      product_bind (product_native _ (fun _ => bounded_peer_put (some pid))) (fun _ =>
      product_bind softirq (fun _ => product_pure _)))

theorem decrypt_iteration : ProductSafe (Driver.decryptIterObserved Journal.hooks) :=
  workerIterPrefix_preserves _ _ (fun _ _ hi => hi.2) decrypt_step (resched _ _)

end Leanux.Proofs.WG.HandshakeSecurity.ReceiveMaterial.Execution
