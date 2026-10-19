import Leanux.Proofs.WG.TransmitSecurity.DriverFixtureNeutral
import Leanux.Proofs.WG.HandshakeSecurity.ReceiveMaterialDeferred
import Leanux.Proofs.WG.HandshakeSecurity.ReceiveMaterialIngress
import Leanux.Proofs.WG.Lifetimes.TrafficPreservation

/-! Fixture traffic shares the same RX allocation journal through ingress,
inline receive polling, stack replies and deferred send callbacks. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.ReceiveMaterial.Execution
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do
open Lifetimes Queues TransmitSecurity Responder

theorem ingress (msg : List UInt8) (src : SkbSource) :
    ProductSafe (Driver.receiveEntryObserved msg src) := by
  simpa only [Driver.receiveEntryObserved,liftWGObserver_lift] using
    product_state (state_native _ (fun _ => IngressFrames.receive msg src))

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
    (same : wgStoreView v.wg = wgStoreView w.wg) (hi : Carrier h w.wg) : Carrier h v.wg :=
  ⟨bounded_device (congrArg WGStoreView.dev same) hi.1,hi.2⟩

theorem inject (family port : Nat) (msg : List UInt8) (tos : Nat) (ll : Bool) (dest : Nat) :
    ProductSafe (Driver.injectObserved Journal.hooks family port msg tos ll dest) :=
  TrafficSource.inject_preserves (fun _ _ hi => hi.2) product_stable _ _ _ ingress crypt drain
    family port msg tos ll dest

theorem after_batch : ProductSafe (Driver.afterBatchObserved Journal.hooks) :=
  TrafficSource.afterBatch_preserves (fun _ _ hi => hi.2) product_stable _ _ _ _ _ crypt send_workers
    (by rw [Driver.sendWorker_lift _ rfl]; exact send_one) schedule drain

theorem flood (count port family : Nat) (messages : List (List UInt8)) :
    ProductSafe (Driver.floodObserved Journal.hooks count port family messages) :=
  TrafficSource.flood_preserves (fun _ _ hi => hi.2) product_stable _ _ _ _ ingress inline_poll
    after_batch drain count port family messages

theorem batch_item (d : Device) (cqes : List Int) (item : Env.BatchItem) :
    ProductSafe (Driver.batchItemObserved Journal.hooks d cqes item) := by
  unfold Driver.batchItemObserved
  simp only [Journal.fixture_neutral,AuthenticatedEffects.FixtureEffects.run_neutral]
  exact batchItemWith_preserves (fun _ _ hi => hi.2) product_wg_store _ _ _ _ ingress inline_poll multicast
    (fun family addr packets mtu => product_state (transmit family addr packets mtu)) d cqes item

theorem batch (items : List Env.BatchItem) : ProductSafe (Driver.batchObserved Journal.hooks items) :=
  TrafficSource.batch_preserves (fun _ _ hi => hi.2) product_stable _ _ batch_item after_batch items

theorem syscall_xmit (family addr : Nat) (payload : List UInt8) (opts : Env.XmitOpts) :
    ProductSafe (Driver.syscallXmitObserved Journal.hooks family addr payload opts) := by
  unfold Driver.syscallXmitObserved
  simp only [Journal.fixture_neutral,AuthenticatedEffects.FixtureEffects.run_neutral]
  exact syscallXmitWith_preserves (fun _ _ hi => hi.2) product_wg_store _ _ multicast
    (fun family addr packets mtu => product_state (transmit family addr packets mtu)) family addr payload opts

end Leanux.Proofs.WG.HandshakeSecurity.ReceiveMaterial.Execution
