import Leanux.Proofs.WG.HandshakeSecurity.TimestampArchiveNapi
import Leanux.Proofs.WG.HandshakeSecurity.TimestampArchiveWorker

/-! The original decrypt worker carries timestamp history through publication,
both native NAPI paths and repayment of its publication peer reference. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.TimestampArchive
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues TransmitSecurity

theorem decrypt (pkt : RxPacket) (history : List TimestampReceipt) :
    Framing.Preserves (StateInv history) (decryptPacket pkt) := by
  unfold decryptPacket WG.orM
  simp (config := {zeta := false}) only [branch,branchCmp,hiddenAlloc,invariant]
  repeat' archive_poll_step history

theorem rx_publish (id : SkbId) (state : PacketState) (history : List TimestampReceipt) :
    Framing.Preserves (StateInv history) (RxWorkers.publishSource id state) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a pid v b hi run
  obtain ⟨d,pkt,key,p,hd,_,_,_,hp,effect⟩ :=
    PublicationIdentity.publish_execution id state w v a b pid run
  have device := congrArg WGStoreView.dev effect
  have frontier := congrArg WGStoreView.peerCounter effect
  apply state_retained hi
  · intro q stamp found
    change v.dev = some _ at device
    by_cases eq : pid = q
    · subst q
      simpa [freshnessAt,device,hd,hp] using found
    · simpa [freshnessAt,device,hd,Std.TreeMap.getElem?_insert,eq] using found
  · change v.peerCounter = w.peerCounter at frontier
    rw [frontier]
    exact Nat.le_refl _

theorem prepare_worker (history : List TimestampReceipt) :
    Framing.Preserves (StateInv history) RxWorkers.prepareSource := by
  unfold RxWorkers.prepareSource
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (rx_retention_head decryptPacket; exact decrypt _ history)
    | (rx_retention_head RxWorkers.publishSource; exact rx_publish _ _ history)
    | (rx_retention_head setRxSkb; exact skb _ history)
    | archive_poll_step history

theorem product_native (action : WG.M α)
    (preserved : ∀ history, Framing.Preserves (StateInv history) action) :
    ProductPreserves (liftPrefix (liftWG action)) :=
  product_lift _ (fun history => PublicationPoll.native_product _ _ (preserved history))

theorem product_ambient (action : AmbientM α) :
    ProductPreserves (liftPrefix (monadLift action : Leanux.M α)) :=
  product_lift _ (fun _ => productAmbient_spec action _ (fun _ _ hi => hi))

theorem resched (worker : Worker) (site : Decision) :
    ProductPreserves (Driver.reschedObserved worker site) :=
  PrefixPreserves.bind (product_store _ (condResched_sameKernel worker))
    (fun _ => product_ambient _)

theorem decrypt_step : ProductPreserves (Driver.decryptStepObserved TimestampDriver.hooks) := by
  unfold Driver.decryptStepObserved RxWorkers.decryptWith
  apply PrefixPreserves.bind softirq
  intro _
  apply PrefixPreserves.bind (product_native _ prepare_worker)
  intro item
  cases item with
  | none => exact product_pure _
  | some pid =>
    exact PrefixPreserves.bind irq_exit (fun _ =>
      PrefixPreserves.bind (product_native _ (peer_put (some pid))) (fun _ =>
        PrefixPreserves.bind softirq (fun _ => product_pure _)))

theorem decrypt_iteration : ProductPreserves (Driver.decryptIterObserved TimestampDriver.hooks) :=
  workerIterPrefix_preserves _ _ (fun _ _ hi => hi.1) decrypt_step (resched _ _)

theorem receive_iteration : ProductPreserves (Driver.receiveIterObserved TimestampDriver.hooks) :=
  workerIterPrefix_preserves _ _ (fun _ _ hi => hi.1) (product_safe handshake_worker)
    (product_store _ (condResched_sameKernel _))

end Leanux.Proofs.WG.HandshakeSecurity.TimestampArchive
