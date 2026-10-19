import Leanux.Proofs.WG.AuthenticatedEffects.CausalDelayedDisposalFrames
import Leanux.Proofs.WG.AuthenticatedEffects.CausalDelayedPoll

/-! Source composition through every actual packet/handshake worker iteration.
Each nested NAPI and socket callback retains the same live delayed carrier. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Delayed
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes
open TransmitSecurity Queues

theorem product_store_lift (action : Leanux.M α) (frame : SameProductStore action) :
    ProductSafe (liftPrefix action) :=
  viewLiftPrefix_preserves productStoreView (fun _ _ _ => True.intro) product_store frame

theorem product_ambient (action : AmbientM α) :
    ProductSafe (liftPrefix (monadLift action : Leanux.M α)) :=
  product_store_lift _ (fun _ => productAmbient_spec action _ (fun _ _ hi => hi))

theorem resched (worker : Worker) (site : Decision) : ProductSafe (Driver.reschedObserved worker site) := by
  unfold Driver.reschedObserved
  exact product_bind (product_store_lift _ (condResched_sameKernel worker))
    (fun yes => product_ambient (AmbientM.branch site yes))

theorem encrypt_tail (item : Option (List SkbId)) : ProductSafe (Driver.encryptTailObserved hooks item) :=
  workerIterPrefix_preserves .encryptWorker none (fun _ _ _ => True.intro) (encrypt item)
    (resched .encryptWorker .encWorkerNeedResched)

theorem encrypt_iter : ProductSafe (Driver.encryptIterObserved hooks) :=
  product_bind poll (fun item => product_bind softirq (fun _ => encrypt_tail item))

theorem tx_iter (pid : PeerId) : ProductSafe (Driver.txIterObserved hooks pid) :=
  workerIterPrefix_preserves .txWorker (some pid) (fun _ _ _ => True.intro) (transmit pid)
    (resched .txWorker .txNeedResched)

theorem decrypt_step : ProductSafe (Driver.decryptStepObserved hooks) := by
  unfold Driver.decryptStepObserved RxWorkers.decryptWith
  apply product_bind softirq
  intro _
  apply product_bind decrypt_prepare
  intro peer
  cases peer with
  | none => exact product_pure _
  | some pid =>
    apply product_bind irq_exit
    intro _
    apply product_bind
    · exact product_state (peer_release _)
    · intro _
      exact product_bind softirq (fun _ => product_pure _)

theorem decrypt_iter : ProductSafe (Driver.decryptIterObserved hooks) :=
  workerIterPrefix_preserves .decryptWorker none (fun _ _ _ => True.intro) decrypt_step
    (resched .decryptWorker .decWorkerNeedResched)

theorem receive_iter : ProductSafe (Driver.receiveIterObserved hooks) :=
  workerIterPrefix_preserves .receiveWorker none (fun _ _ _ => True.intro) (product_state handshake_worker)
    (product_store_lift _ (condResched_sameKernel .receiveWorker))

end Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Delayed
