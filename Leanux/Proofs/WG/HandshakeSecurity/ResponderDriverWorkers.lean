import Leanux.Proofs.WG.HandshakeSecurity.ResponderDriverWorkerFrames

/-! Committed encrypt, decrypt and transmit worker iterations carry the shared
responder history through their actual NAPI callbacks and scheduling cuts. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.Responder.DriverCuts
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes Queues TransmitSecurity

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

theorem encrypt_tail (item : Option (List SkbId)) :
    ProductPreserves (Driver.encryptTailObserved hooks item) :=
  workerIterPrefix_preserves _ _ (fun _ _ hi => hi.2)
    (product_lift _ (carrier_encrypt_tail item)) (resched _ _)

theorem encrypt_iteration (H1 : H1ResponderCurrentEdges) :
    ProductPreserves (Driver.encryptIterObserved hooks) := by
  unfold Driver.encryptIterObserved
  dsimp only [hooks]
  exact PrefixPreserves.bind (product_native _ carrier_encrypt_poll) (fun _ =>
    PrefixPreserves.bind (softirq H1) (fun _ => encrypt_tail _))

theorem tx_iteration (pid : PeerId) : ProductPreserves (Driver.txIterObserved hooks pid) :=
  workerIterPrefix_preserves _ _ (fun _ _ hi => hi.2)
    (product_native _ (carrier_tx_step pid)) (resched _ _)

theorem decrypt_step (H1 : H1ResponderCurrentEdges) :
    ProductPreserves (Driver.decryptStepObserved hooks) := by
  unfold Driver.decryptStepObserved RxWorkers.decryptWith
  apply PrefixPreserves.bind (softirq H1)
  intro _
  apply PrefixPreserves.bind (product_native _ carrier_prepare_worker)
  intro item
  cases item with
  | none => exact product_pure _
  | some pid =>
    exact PrefixPreserves.bind (irq_exit H1) (fun _ =>
      PrefixPreserves.bind (product_native _ (carrier_peer_put (some pid))) (fun _ =>
        PrefixPreserves.bind (softirq H1) (fun _ => product_pure _)))

theorem decrypt_iteration (H1 : H1ResponderCurrentEdges) :
    ProductPreserves (Driver.decryptIterObserved hooks) :=
  workerIterPrefix_preserves _ _ (fun _ _ hi => hi.2) (decrypt_step H1) (resched _ _)

end Leanux.Proofs.WG.HandshakeSecurity.Responder.DriverCuts
