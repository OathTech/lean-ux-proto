import Leanux.Proofs.WG.AuthenticatedEffects.CausalSelectionLifecycle
import Leanux.Proofs.WG.AuthenticatedEffects.CausalSelectionDeferred

/-! Traffic callbacks preserve same-run delayed selection evidence through
actual interleaved ingress, NAPI, transmission and scheduler calls. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Selections.Carrier
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do
open Lifetimes Queues TransmitSecurity.Driver

theorem ingress (msg : List UInt8) (src : SkbSource) : ProductSafe (receiveEntryObserved msg src) :=
  product_native _ (Delayed.ingress msg src)

theorem multicast (family addr : Nat) : ProductSafe (multicastObserved family addr) :=
  product_native _ (Delayed.multicast family addr)

theorem drain (what : String) (flags : List Bool) : ProductSafe (drainObserved what flags) :=
  product_native _ (Delayed.drain what flags)

theorem product_wg_store (h : List Event) (w v : World)
    (same : wgStoreView v.wg = wgStoreView w.wg) (input : Inv h w.wg) : Inv h v.wg :=
  ⟨Delayed.product_wg_store h w v same input.1,input.2⟩

private theorem safe (h : List Event) (w : World) (input : Inv h w.wg) : Safe h := input.2

theorem inject (family port : Nat)
    (msg : List UInt8) (tos : Nat) (ll : Bool) (dest : Nat) :
    ProductSafe (injectObserved hooks family port msg tos ll dest) :=
  TrafficSource.inject_preserves safe product_store _ _ _ ingress crypt drain family port msg tos ll dest

theorem afterBatch :
    ProductSafe (afterBatchObserved hooks) :=
  DeliverySource.afterBatch_preserves safe product_store _ _ _ _ _ _ crypt sendWorkers
    Selections.send_worker schedule drain deliver

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

end Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Selections.Carrier
