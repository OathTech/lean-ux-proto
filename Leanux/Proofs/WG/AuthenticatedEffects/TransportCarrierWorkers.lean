import Leanux.Proofs.WG.AuthenticatedEffects.TransportCarrierStack

/-! Real encryption, transmission, decryption and handshake worker iterations
retain the shared RX carrier at every supplied native callback. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.TransportCarrier
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes Queues TransmitSecurity.Driver
variable {E : Type} {extra : List E → Prop}
  {origin : E → Option TransportDriver.OriginEvent} {replay : E → Option TransportDriver.Replay}
  {hooks : Hooks E}

structure WorkerSafe (extra : List E → Prop) (origin : E → Option TransportDriver.OriginEvent)
    (replay : E → Option TransportDriver.Replay) (hooks : Hooks E) : Prop where
  prepare : ProductSafe extra origin replay hooks.prepare
  poll : ProductSafe extra origin replay hooks.poll
  encrypt : ∀ item, ProductSafe extra origin replay (hooks.encrypt item)
  transmit : ∀ pid, ProductSafe extra origin replay (hooks.transmit pid)
  handshake : StateSafe extra origin replay (handshakeObserved hooks)
  napi : ∀ pid budget, ProductSafe extra origin replay (nativePollObserved hooks pid budget)

theorem product_storeLift (action : Leanux.M α) (frame : SameProductStore action) :
    ProductSafe extra origin replay (liftPrefix action) :=
  viewLiftPrefix_preserves productStoreView (fun _ _ hi => hi.2) product_store frame

theorem product_ambient (action : AmbientM α) :
    ProductSafe extra origin replay (liftPrefix (MonadLift.monadLift action : Leanux.M α)) :=
  product_storeLift _ (fun _ => productAmbient_spec action _ (fun _ _ hi => hi))

theorem product_wg (action : WG.M α) (frame : SameView RxDisposition.nativeRxStore action) :
    ProductSafe extra origin replay (liftPrefix (liftWG action)) := by
  simpa only [liftWGObserver_lift] using product_state (extra := extra) (origin := origin)
    (replay := replay) (state_rx action frame)

theorem resched (worker : Worker) (site : Decision) :
    ProductSafe extra origin replay (reschedObserved worker site) := by
  unfold reschedObserved
  exact product_bind (product_storeLift _ (condResched_sameKernel worker))
    (fun yes => product_ambient (AmbientM.branch site yes))

theorem encryptTail (h : WorkerSafe extra origin replay hooks) (item : Option (List SkbId)) :
    ProductSafe extra origin replay (encryptTailObserved hooks item) :=
  workerIterPrefix_preserves .encryptWorker none (fun _ _ hi => hi.2) (h.encrypt item)
    (resched .encryptWorker .encWorkerNeedResched)

theorem encryptIter (h : WorkerSafe extra origin replay hooks) :
    ProductSafe extra origin replay (encryptIterObserved hooks) :=
  product_bind h.poll (fun item => product_bind (softirq h.napi) (fun _ => encryptTail h item))

theorem txIter (h : WorkerSafe extra origin replay hooks) (pid : PeerId) :
    ProductSafe extra origin replay (txIterObserved hooks pid) :=
  workerIterPrefix_preserves .txWorker (some pid) (fun _ _ hi => hi.2) (h.transmit pid)
    (resched .txWorker .txNeedResched)

theorem decryptStep (h : WorkerSafe extra origin replay hooks) :
    ProductSafe extra origin replay (decryptStepObserved hooks) := by
  unfold decryptStepObserved RxWorkers.decryptWith
  apply product_bind (softirq h.napi)
  intro _
  apply product_bind h.prepare
  intro peer
  cases peer with
  | none => exact product_pure _
  | some pid =>
    exact product_bind (irqExit h.napi) (fun _ =>
      product_bind (product_wg _ (RxCredits.peerPut_rxView (some pid))) (fun _ =>
      product_bind (softirq h.napi) (fun _ => product_pure _)))

theorem decryptIter (h : WorkerSafe extra origin replay hooks) :
    ProductSafe extra origin replay (decryptIterObserved hooks) :=
  workerIterPrefix_preserves .decryptWorker none (fun _ _ hi => hi.2) (decryptStep h)
    (resched .decryptWorker .decWorkerNeedResched)

theorem receiveIter (h : WorkerSafe extra origin replay hooks) :
    ProductSafe extra origin replay (receiveIterObserved hooks) :=
  workerIterPrefix_preserves .receiveWorker none (fun _ _ hi => hi.2) (product_state h.handshake)
    (product_storeLift _ (condResched_sameKernel .receiveWorker))

end Leanux.Proofs.WG.AuthenticatedEffects.TransportCarrier
