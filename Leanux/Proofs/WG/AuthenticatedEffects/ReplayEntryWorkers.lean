import Leanux.Proofs.WG.AuthenticatedEffects.ReplayEntryPoll
import Leanux.Proofs.WG.AuthenticatedEffects.ReplayEntryWorkerFrames

/-! Actual worker source transport, retaining counter-entry certificates from
NAPI callbacks even when later work stops. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.ReplayEntry
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes Queues Keypairs TransmitSecurity.Driver

theorem product_storeLift (action : Leanux.M α) (frame : SameProductStore action) :
    ProductSafe (liftPrefix action) :=
  viewLiftPrefix_preserves productStoreView (fun _ _ hi => hi.2) product_store frame

theorem product_ambient (action : AmbientM α) :
    ProductSafe (liftPrefix (monadLift action : Leanux.M α)) :=
  product_storeLift _ (fun _ => productAmbient_spec action _ (fun _ _ hi => hi))

theorem product_wg (action : WG.M α) (frame : OrdinaryAction action) :
    ProductSafe (liftPrefix (liftWG action)) := by
  simpa only [liftWGObserver_lift] using product_state (state_native action frame)

theorem resched (worker : Worker) (site : Decision) : ProductSafe (reschedObserved worker site) := by
  unfold reschedObserved
  exact product_bind (product_same _ (EnvFrames.condResched_sameSnapshot worker))
    (fun yes => product_ambient (AmbientM.branch site yes))

theorem encrypt_tail (item : Option (List SkbId)) : ProductSafe (encryptTailObserved hooks item) :=
  workerIterPrefix_preserves .encryptWorker none (fun _ _ hi => hi.2)
    (product_native _ (encrypt_ordinary item)) (resched .encryptWorker .encWorkerNeedResched)

theorem encrypt_iteration : ProductSafe (encryptIterObserved hooks) :=
  product_bind (product_wg _ poll_ordinary) (fun item =>
    product_bind softirq (fun _ => encrypt_tail item))

theorem tx_iteration (pid : PeerId) : ProductSafe (txIterObserved hooks pid) :=
  workerIterPrefix_preserves .txWorker (some pid) (fun _ _ hi => hi.2)
    (product_wg _ (SchedulerObservers.txStep_ordinary pid)) (resched .txWorker .txNeedResched)

theorem decrypt_step : ProductSafe (decryptStepObserved hooks) := by
  unfold decryptStepObserved RxWorkers.decryptWith
  apply product_bind softirq
  intro _
  apply product_bind (product_wg _ prepare_ordinary)
  intro peer
  cases peer with
  | none => exact product_pure _
  | some pid =>
    exact product_bind irq_exit (fun _ =>
      product_bind (product_state (state_same _ (WGFrames.peerPut_sameSnapshot (some pid)))) (fun _ =>
      product_bind softirq (fun _ => product_pure _)))

theorem decrypt_iteration : ProductSafe (decryptIterObserved hooks) :=
  workerIterPrefix_preserves .decryptWorker none (fun _ _ hi => hi.2)
    decrypt_step (resched .decryptWorker .decWorkerNeedResched)

theorem receive_iteration : ProductSafe (receiveIterObserved hooks) :=
  workerIterPrefix_preserves .receiveWorker none (fun _ _ hi => hi.2)
    (product_state handshake) (product_same _ (EnvFrames.condResched_sameSnapshot .receiveWorker))

end Leanux.Proofs.WG.AuthenticatedEffects.ReplayEntry
