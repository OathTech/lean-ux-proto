import Leanux.Proofs.WG.TransmitSecurity.EncryptionHistoryDeferred

/-! Fixture traffic and generated Stack responses preserve historical
encryption exclusion in the same shared execution. -/
namespace Leanux.Proofs.WG.TransmitSecurity.EncryptionHistory.Scheduler
set_option maxHeartbeats 600000
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open RetirementSecurity Queues.RxCredits

theorem ingress (msg : List UInt8) (src : SkbSource) : ProductSafe (Driver.receiveEntryObserved msg src) :=
  product_native _ (fun _ => native_join (EncryptionPast.Ingress.receive msg src)
    (RxPollOccurrences.join (ReceiveIngressCall.erases (.udp msg src)) (ReceiveIngressCall.allocation (.udp msg src))
      (ReceiveOccurrences.receive msg src)))

theorem inline_poll : ProductSafe (Driver.inlinePollObserved Journal.hooks) := by
  apply product_checked
  · intro past
    exact (show Driver.inlinePollObserved Quiet.nonencryptHooks = Driver.inlinePollObserved Journal.hooks from rfl) ▸
      Driver.inline_history Quiet.hooks_safe.actors
  · intro past w h result v before run
    have projected := Driver.inline_projects Journal.hooks_projects
    rw [Driver.nonce_inlinePollObserved_eq] at projected
    exact (hoare_iff_run _ _ _).mp (product_join EncryptionPast.Napi.inline (OccurrenceNapi.inline [] [])) w result v before
      (DriverOwnership.product_native projected Nonce.inlinePollObserved_erases w v h run)

theorem transmit (family addr : Nat) (packets : List WG.Packet) (mtu : Nat) :
    StateSafe (Driver.transmitObserved Journal.hooks family addr packets mtu) := by
  apply state_checked
  · intro past
    exact (show Driver.transmitObserved Quiet.nonencryptHooks family addr packets mtu =
        Driver.transmitObserved Journal.hooks family addr packets mtu from rfl) ▸
      Driver.transmit_history Quiet.hooks_safe.core family addr packets mtu
  · intro past w a h result v b before run
    have projected := Driver.transmit_projects Journal.hooks_projects family addr packets mtu
    rw [Driver.nonce_transmitObserved_eq] at projected
    have native := DriverOwnership.state_native projected (Nonce.transmitObserved_erases family addr packets mtu)
      w v a b h run
    exact ⟨(hoare_iff_run_ambient _ _ _).mp (EncryptionPast.transmit family addr packets mtu)
      w a result v b before.1 native,
      before.2.1.transmit family addr packets mtu a b native,
      TransmitOccurrences.transmit ⟨before.2.1.bounded,before.2.2⟩ family addr packets mtu a b native⟩

theorem multicast (family addr : Nat) :
    ProductSafe (Driver.multicastObserved family addr) := by
  apply product_store
  intro initial
  change Framing.Preserves (fun w : World => productStoreView w = initial) _
  have loop : Framing.Preserves (fun w : World => productStoreView w = initial)
      (monadLift (loopbackSend [] true) : Leanux.M Unit) :=
    liftWG_sameProductStore _ (loopbackSend_kernel [] true) initial
  have ambient {α : Type} (a : AmbientM α) :
      Framing.Preserves (fun w : World => productStoreView w = initial) (monadLift a : Leanux.M α) :=
    productAmbient_spec a _ (fun _ _ hi => hi)
  routing_tx_source [Env.xmitMulticastLoop] using [loop,ambient]

theorem drain (what : String) (flags : List Bool) :
    ProductSafe (Driver.drainObserved what flags) :=
  product_store _ (Nonce.Frames.drained what flags)

theorem product_wg_store (h : List Journal.Event) (w v : World)
    (same : wgStoreView v.wg = wgStoreView w.wg) (hi : (Inv []) h w) : (Inv []) h v :=
  ⟨by
      have device := congrArg WGStoreView.dev same
      have epochs := congrArg WGStoreView.netIfindexNext same
      change v.wg.dev = w.wg.dev at device
      change v.wg.netIfindexNext = w.wg.netIfindexNext at epochs
      simpa only [EncryptionPast.Ready,TxDisposition.LiveFrontier.Ready,
        TxDisposition.LiveFrontier.Inv,TxDisposition.LiveFrontier.Physical,
        EncryptionPast.view,device,epochs] using hi.1,
    OccurrenceStack.ready_store same hi.2⟩

theorem inject (family port : Nat) (msg : List UInt8) (tos : Nat) (ll : Bool) (dest : Nat) :
    ProductSafe (Driver.injectObserved Journal.hooks family port msg tos ll dest) :=
  TrafficSource.inject_preserves (fun _ _ hi => EncryptionHistory.safe hi) product_stable _ _ _ ingress crypt drain
    family port msg tos ll dest

theorem after_batch : ProductSafe (Driver.afterBatchObserved Journal.hooks) :=
  TrafficSource.afterBatch_preserves (fun _ _ hi => EncryptionHistory.safe hi) product_stable _ _ _ _ _ crypt send_workers
    (by rw [Driver.sendWorker_lift Journal.hooks rfl]; exact send_one) schedule drain

theorem flood (count port family : Nat) (messages : List (List UInt8)) :
    ProductSafe (Driver.floodObserved Journal.hooks count port family messages) :=
  TrafficSource.flood_preserves (fun _ _ hi => EncryptionHistory.safe hi) product_stable _ _ _ _ ingress inline_poll
    after_batch drain count port family messages

private theorem fixture_neutral :
    Driver.fixtureOps Journal.hooks = AuthenticatedEffects.FixtureEffects.neutral := rfl

theorem batch_item (d : Device) (cqes : List Int) (item : Env.BatchItem) :
    ProductSafe (Driver.batchItemObserved Journal.hooks d cqes item) := by
  unfold Driver.batchItemObserved
  simp only [fixture_neutral, AuthenticatedEffects.FixtureEffects.run_neutral]
  exact batchItemWith_preserves (fun _ _ hi => EncryptionHistory.safe hi) product_wg_store _ _ _ _ ingress inline_poll multicast
    (fun family addr packets mtu => state_product (transmit family addr packets mtu)) d cqes item

theorem batch (items : List Env.BatchItem) : ProductSafe (Driver.batchObserved Journal.hooks items) :=
  TrafficSource.batch_preserves (fun _ _ hi => EncryptionHistory.safe hi) product_stable _ _ batch_item after_batch items

theorem syscall_xmit (family addr : Nat) (payload : List UInt8) (opts : Env.XmitOpts) :
    ProductSafe (Driver.syscallXmitObserved Journal.hooks family addr payload opts) := by
  unfold Driver.syscallXmitObserved
  simp only [fixture_neutral, AuthenticatedEffects.FixtureEffects.run_neutral]
  exact syscallXmitWith_preserves (fun _ _ hi => EncryptionHistory.safe hi) product_wg_store _ _ multicast
    (fun family addr packets mtu => state_product (transmit family addr packets mtu)) family addr payload opts

end Leanux.Proofs.WG.TransmitSecurity.EncryptionHistory.Scheduler
