import Leanux.Proofs.WG.HandshakeSecurity.PendingPromotionEncryptionFrames

/-! Committed encrypt, decrypt and transmit worker iterations carry the shared
responder history through their actual NAPI callbacks and scheduling cuts. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.PendingPromotion
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes Queues TransmitSecurity
open Responder.DriverCuts (hooks)

theorem product_native (action : WG.M α)
    (preserves : ∀ confirmed, Framing.Preserves (Carrier confirmed) action) :
    ProductPreserves (liftPrefix (liftWG action)) :=
  product_lift _ (fun confirmed => PublicationPoll.native_product _ _ (preserves confirmed))

theorem product_ambient (action : AmbientM α) :
    ProductPreserves (liftPrefix (monadLift action : Leanux.M α)) :=
  product_lift _ (fun _ => productAmbient_spec action _ (fun _ _ hi => hi))

theorem resched (worker : Worker) (site : Decision) :
    ProductPreserves (Driver.reschedObserved worker site) :=
  PrefixPreserves.bind (product_store _ (condResched_sameKernel worker))
    (fun _ => product_ambient _)

theorem encrypt_tail (publication : H1PublicationFrame) (item : Option (List SkbId)) :
    ProductPreserves (Driver.encryptTailObserved hooks item) :=
  workerIterPrefix_preserves _ _ (fun _ _ hi => hi.2.2.distinct)
    (product_lift _ (Carrier.encrypt_tail publication item)) (resched _ _)

theorem encrypt_iteration (edges : H1PendingPromotionEdges) (quiet : H1PendingQuietFrames)
    (pollFrames : H1PendingPollFrames) (stackFrames : H1PendingStackFrames) (publication : H1PublicationFrame) :
    ProductPreserves (Driver.encryptIterObserved hooks) := by
  unfold Driver.encryptIterObserved
  dsimp only [hooks]
  exact PrefixPreserves.bind (product_native _ Carrier.encrypt_poll) (fun _ =>
    PrefixPreserves.bind (softirq edges quiet pollFrames stackFrames) (fun _ => encrypt_tail publication _))

theorem tx_iteration (frames : H1TransmitFrames) (handshake : H1PendingHandshakeFrames) (pid : PeerId) : ProductPreserves (Driver.txIterObserved hooks pid) :=
  workerIterPrefix_preserves _ _ (fun _ _ hi => hi.2.2.distinct)
    (product_native _ (Carrier.tx_step frames handshake pid)) (resched _ _)

theorem decrypt_step (edges : H1PendingPromotionEdges) (quiet : H1PendingQuietFrames)
    (pollFrames : H1PendingPollFrames) (stackFrames : H1PendingStackFrames) :
    ProductPreserves (Driver.decryptStepObserved hooks) := by
  unfold Driver.decryptStepObserved RxWorkers.decryptWith
  apply PrefixPreserves.bind (softirq edges quiet pollFrames stackFrames)
  intro _
  apply PrefixPreserves.bind (product_native _ Carrier.prepare_worker)
  intro item
  cases item with
  | none => exact product_pure _
  | some pid =>
    exact PrefixPreserves.bind (irq_exit edges quiet pollFrames stackFrames) (fun _ =>
      PrefixPreserves.bind (product_native _ (fun confirmed => Carrier.peer_put confirmed (some pid))) (fun _ =>
        PrefixPreserves.bind (softirq edges quiet pollFrames stackFrames) (fun _ => product_pure _)))

theorem decrypt_iteration (edges : H1PendingPromotionEdges) (quiet : H1PendingQuietFrames)
    (pollFrames : H1PendingPollFrames) (stackFrames : H1PendingStackFrames) :
    ProductPreserves (Driver.decryptIterObserved hooks) :=
  workerIterPrefix_preserves _ _ (fun _ _ hi => hi.2.2.distinct) (decrypt_step edges quiet pollFrames stackFrames) (resched _ _)

theorem receive_iteration (edges : H1PendingPromotionEdges) (quiet : H1PendingQuietFrames)
    (frames : H1PendingHandshakeFrames) : ProductPreserves (Driver.receiveIterObserved hooks) :=
  workerIterPrefix_preserves _ _ (fun _ _ hi => hi.2.2.distinct)
    (product_safe (handshake edges quiet frames)) (product_store _ (condResched_sameKernel _))

end Leanux.Proofs.WG.HandshakeSecurity.PendingPromotion
