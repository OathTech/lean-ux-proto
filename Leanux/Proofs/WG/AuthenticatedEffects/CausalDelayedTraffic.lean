import Leanux.Proofs.WG.AuthenticatedEffects.CausalDelayedIngress
import Leanux.Proofs.WG.AuthenticatedEffects.DeliveryPreservation

/-! Actual fixture ingress, flood, batch and transmit callbacks transport live
delayed occurrences through their interleaved native worker and poll schedule. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Delayed
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do
open Lifetimes Queues TransmitSecurity.Driver
theorem ingress (msg : List UInt8) (src : SkbSource) :
    ProductSafe (receiveEntryObserved msg src) := by
  simpa only [receiveEntryObserved,liftWGObserver_lift] using product_state (udp_receive msg src)

theorem multicast (family addr : Nat) :
    ProductSafe (multicastObserved family addr) := by
  apply product_store_lift
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
    ProductSafe (drainObserved what flags) :=
  product_store_lift _ (TransmitSecurity.Nonce.Frames.drained what flags)

theorem product_wg_store (h : List Event) (w v : World)
    (same : wgStoreView v.wg = wgStoreView w.wg) (hi : Inv h w.wg) : Inv h v.wg := by
  have device := congrArg WGStoreView.dev same
  change v.wg.dev = w.wg.dev at device
  apply hi.retained
  · intro pid timer token pending
    simpa only [TimerSlots.view,device] using pending
  · simp only [QueuedOccurrences.queue,device]

private theorem safe (h : List Event) (w : World) (_ : Inv h w.wg) : True := True.intro

theorem inject (family port : Nat)
    (msg : List UInt8) (tos : Nat) (ll : Bool) (dest : Nat) :
    ProductSafe (injectObserved hooks family port msg tos ll dest) :=
  TrafficSource.inject_preserves safe product_store _ _ _ ingress crypt drain family port msg tos ll dest

theorem afterBatch :
    ProductSafe (afterBatchObserved hooks) :=
  DeliverySource.afterBatch_preserves safe product_store _ _ _ _ _ _ crypt sendWorkers
    send_worker schedule drain deliver

theorem flood (count port family : Nat)
    (messages : List (List UInt8)) :
    ProductSafe (floodObserved hooks count port family messages) :=
  TrafficSource.flood_preserves safe product_store _ _ _ _ ingress inline_poll
    afterBatch drain count port family messages

theorem batchItem
    (d : Device) (cqes : List Int) (item : Env.BatchItem) :
    ProductSafe (batchItemObserved hooks d cqes item) :=
  batchItemWith_preserves safe product_wg_store _ _ _ _ ingress inline_poll multicast
    (fun family addr packets mtu => product_state (fixture _ _
      (device_transmit family addr packets mtu))) d cqes item

theorem batch
    (items : List Env.BatchItem) : ProductSafe (batchObserved hooks items) :=
  TrafficSource.batch_preserves safe product_store _ _ batchItem afterBatch items

theorem syscallXmit
    (family addr : Nat) (payload : List UInt8) (opts : Env.XmitOpts) :
    ProductSafe (syscallXmitObserved hooks family addr payload opts) :=
  syscallXmitWith_preserves safe product_wg_store _ _ multicast
    (fun family addr packets mtu => product_state (fixture _ _
      (device_transmit family addr packets mtu)))
    family addr payload opts

end Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Delayed
