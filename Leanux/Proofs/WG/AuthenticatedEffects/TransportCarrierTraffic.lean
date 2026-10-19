import Leanux.Proofs.WG.AuthenticatedEffects.TransportCarrierIngress
import Leanux.Proofs.WG.AuthenticatedEffects.DeliveryPreservation

/-! Fixture ingress, flood, batch and transmit callers preserve the actual
shared RX publication carrier, including interleaved inline NAPI callbacks. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.TransportCarrier
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do
open Lifetimes Queues TransmitSecurity.Driver
variable {E : Type} {extra : List E → Prop}
  {origin : E → Option TransportDriver.OriginEvent} {replay : E → Option TransportDriver.Replay}
  {hooks : Hooks E}

theorem multicast (family addr : Nat) :
    ProductSafe extra origin replay (multicastObserved family addr) := by
  apply product_storeLift
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
    ProductSafe extra origin replay (drainObserved what flags) :=
  product_storeLift _ (TransmitSecurity.Nonce.Frames.drained what flags)

theorem product_wg_store (h : List E) (w v : World)
    (same : wgStoreView v.wg = wgStoreView w.wg) (hi : ProductInv extra origin replay h w) :
    ProductInv extra origin replay h v := by
  have dev := congrArg WGStoreView.dev same
  change v.wg.dev = w.wg.dev at dev
  exact ⟨hi.1.sameRx (by simp only [RxDisposition.nativeRxStore,dev]),hi.2⟩

private theorem safe (h : List E) (w : World) (hi : ProductInv extra origin replay h w) :
    TransportReplay.Safe origin replay h ∧ extra h := hi.2

theorem inject (h : DeferredSafe extra origin replay hooks) (family port : Nat)
    (msg : List UInt8) (tos : Nat) (ll : Bool) (dest : Nat) :
    ProductSafe extra origin replay (injectObserved hooks family port msg tos ll dest) :=
  TrafficSource.inject_preserves safe product_store _ _ _ (receive_entry_nested h.peerRelease) (crypt h) drain family port msg tos ll dest

theorem afterBatch (h : DeferredSafe extra origin replay hooks) :
    ProductSafe extra origin replay (afterBatchObserved hooks) :=
  DeliverySource.afterBatch_preserves safe product_store _ _ _ _ _ _ (crypt h) (sendWorkers h)
    h.sendWorker (schedule h.toWorkerSafe) drain h.deliver

theorem flood (h : DeferredSafe extra origin replay hooks) (count port family : Nat)
    (messages : List (List UInt8)) :
    ProductSafe extra origin replay (floodObserved hooks count port family messages) :=
  TrafficSource.flood_preserves safe product_store _ _ _ _ (receive_entry_nested h.peerRelease) (inlinePoll h.napi)
    (afterBatch h) drain count port family messages

theorem batchItem (h : DeferredSafe extra origin replay hooks)
    (front : ∀ family addr packets mtu, StateSafe extra origin replay (hooks.front family addr packets mtu))
    (d : Device) (cqes : List Int) (item : Env.BatchItem) :
    ProductSafe extra origin replay (batchItemObserved hooks d cqes item) :=
  batchItemWith_preserves safe product_wg_store _ _ _ _ (receive_entry_nested h.peerRelease) (inlinePoll h.napi) multicast
    (fun family addr packets mtu => product_state (fixture h.toStagingSafe _ _
      (transmit h.toStagingSafe front family addr packets mtu))) d cqes item

theorem batch (h : DeferredSafe extra origin replay hooks)
    (front : ∀ family addr packets mtu, StateSafe extra origin replay (hooks.front family addr packets mtu))
    (items : List Env.BatchItem) : ProductSafe extra origin replay (batchObserved hooks items) :=
  TrafficSource.batch_preserves safe product_store _ _ (batchItem h front) (afterBatch h) items

theorem syscallXmit (h : DeferredSafe extra origin replay hooks)
    (front : ∀ family addr packets mtu, StateSafe extra origin replay (hooks.front family addr packets mtu))
    (family addr : Nat) (payload : List UInt8) (opts : Env.XmitOpts) :
    ProductSafe extra origin replay (syscallXmitObserved hooks family addr payload opts) :=
  syscallXmitWith_preserves safe product_wg_store _ _ multicast
    (fun family addr packets mtu => product_state (fixture h.toStagingSafe _ _
      (transmit h.toStagingSafe front family addr packets mtu)))
    family addr payload opts

end Leanux.Proofs.WG.AuthenticatedEffects.TransportCarrier
