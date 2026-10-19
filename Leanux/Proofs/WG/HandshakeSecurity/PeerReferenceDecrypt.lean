import Leanux.Proofs.WG.HandshakeSecurity.PeerReferenceNapi
import Leanux.Proofs.WG.HandshakeSecurity.PeerReferenceWorker

/-! Native receive workers retain positive resident peers through decryption,
publication, NAPI callbacks and repayment of their temporary reference. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.PeerReference
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues TransmitSecurity

theorem decrypt (pkt : RxPacket)  :
    Framing.Preserves Inv (decryptPacket pkt) := by
  unfold decryptPacket WG.orM
  simp (config := {zeta := false}) only [branch,branchCmp,hiddenAlloc,invariant]
  repeat' peer_reference_poll_step

theorem rx_publish (id : SkbId) (state : PacketState) :
    Framing.Preserves Inv (RxWorkers.publishSource id state) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a pid v b before run
  obtain ⟨d,pkt,key,p,device,_,_,_,found,effect⟩ :=
    PublicationIdentity.publish_execution id state w v a b pid run
  have output := congrArg WGStoreView.dev effect
  change v.dev = some _ at output
  apply of_residents
  intro actual other q current stored
  have same := Option.some.inj (output.symm.trans current)
  subst actual
  by_cases equal : pid = other
  · subst other
    have same : {p with refcount := p.refcount + 1,napiScheduled := true} = q := by
      simpa using stored
    subst q
    simp
  · exact resident before device (by simpa [Std.TreeMap.getElem?_insert,equal] using stored)

theorem prepare_worker  :
    Framing.Preserves Inv RxWorkers.prepareSource := by
  unfold RxWorkers.prepareSource
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (rx_retention_head decryptPacket; exact decrypt _)
    | (rx_retention_head RxWorkers.publishSource; exact rx_publish _ _)
    | (rx_retention_head setRxSkb; exact skb _)
    | peer_reference_poll_step

theorem product_native (action : WG.M α) (preserved : Framing.Preserves Inv action) :
    ProductPreserves (liftPrefix (liftWG action)) :=
  product_lift _ (PublicationPoll.native_product _ _ preserved)

theorem product_ambient (action : AmbientM α) :
    ProductPreserves (liftPrefix (monadLift action : Leanux.M α)) :=
  product_lift _ (productAmbient_spec action _ (fun _ _ hi => hi))

theorem resched (worker : Worker) (site : Decision) :
    ProductPreserves (Driver.reschedObserved worker site) :=
  PrefixPreserves.bind (product_store _ (condResched_sameKernel worker))
    (fun _ => product_ambient _)

theorem decrypt_step : ProductPreserves (Driver.decryptStepObserved ExchangeDriver.hooks) := by
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

theorem decrypt_iteration : ProductPreserves (Driver.decryptIterObserved ExchangeDriver.hooks) :=
  workerIterPrefix_preserves _ _ (fun _ _ hi => hi.1) decrypt_step (resched _ _)

theorem receive_iteration : ProductPreserves (Driver.receiveIterObserved ExchangeDriver.hooks) :=
  workerIterPrefix_preserves _ _ (fun _ _ hi => hi.1) (product_safe handshake_worker)
    (product_store _ (condResched_sameKernel _))

end Leanux.Proofs.WG.HandshakeSecurity.PeerReference
