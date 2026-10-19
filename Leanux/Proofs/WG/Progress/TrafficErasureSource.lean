import Leanux.Proofs.WG.Lifetimes.TrafficPreservation
import Leanux.Proofs.WG.Noise.DriverTagDeferredSource

/-! Callback-parametric erasure rules extracted once from the campaign-owned
traffic composition. The operational factories remain the shared originals. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.TrafficErasure
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues
variable {E : Type}

theorem inject
    (receive : List UInt8 → SkbSource → PrefixM E Unit)
    (crypt : PrefixM E Unit) (drained : String → List Bool → PrefixM E Unit)
    (hr : ∀ msg src, ErasesPrefix (receive msg src) (liftWG (wgReceive msg src)))
    (hc : ErasesPrefix crypt Env.runCryptWorkers)
    (hd : ∀ what queues, ErasesPrefix (drained what queues) (Env.requireDrained what queues))
    (family port : Nat) (msg : List UInt8) (tos : Nat) (ll : Bool) (dest : Nat) :
    ErasesPrefix (TrafficSource.injectWith receive crypt drained family port msg tos ll dest)
      (Env.inject family port msg tos ll dest) := by
  unfold TrafficSource.injectWith Env.inject
  repeat' first
    | (tag_deferred_erase_at atom receive; exact hr _ _)
    | (tag_deferred_erase_at atom crypt; exact hc)
    | (tag_deferred_erase_at atom drained; exact hd _ _)
    | rx_env_traffic_erasure

theorem afterBatch
    (crypt send sendOne : PrefixM E Unit) (schedule : Option Worker → PrefixM E Unit)
    (drained : String → List Bool → PrefixM E Unit)
    (hc : ErasesPrefix crypt Env.runCryptWorkers)
    (hs : ErasesPrefix send Env.runSendWorkers)
    (ho : ErasesPrefix sendOne Env.runOneSendWorker)
    (hsch : ∀ stack, ErasesPrefix (schedule stack) (Env.schedule stack))
    (hd : ∀ what queues, ErasesPrefix (drained what queues) (Env.requireDrained what queues)) :
    ErasesPrefix (TrafficSource.afterBatchWith crypt send sendOne schedule drained) Env.afterBatch := by
  unfold TrafficSource.afterBatchWith Env.afterBatch
  repeat' first
    | (tag_deferred_erase_at atom crypt; exact hc)
    | (tag_deferred_erase_at atom send; exact hs)
    | (tag_deferred_erase_at atom sendOne; exact ho)
    | (tag_deferred_erase_at atom schedule; exact hsch _)
    | (tag_deferred_erase_at atom drained; exact hd _ _)
    | rx_env_traffic_erasure

theorem flood
    (receive : List UInt8 → SkbSource → PrefixM E Unit)
    (poll after : PrefixM E Unit) (drained : String → List Bool → PrefixM E Unit)
    (hr : ∀ msg src, ErasesPrefix (receive msg src) (liftWG (wgReceive msg src)))
    (hp : ErasesPrefix poll Env.pollScheduledInline)
    (ha : ErasesPrefix after Env.afterBatch)
    (hd : ∀ what queues, ErasesPrefix (drained what queues) (Env.requireDrained what queues))
    (count port family : Nat) (messages : List (List UInt8)) :
    ErasesPrefix (TrafficSource.floodWith receive poll after drained count port family messages)
      (Env.flood count port family messages) := by
  unfold TrafficSource.floodWith Env.flood
  repeat' first
    | (tag_deferred_erase_at atom receive; exact hr _ _)
    | (tag_deferred_erase_at atom poll; exact hp)
    | (tag_deferred_erase_at atom after; exact ha)
    | (tag_deferred_erase_at atom drained; exact hd _ _)
    | rx_env_traffic_erasure

theorem batchItem
    (receive : List UInt8 → SkbSource → PrefixM E Unit) (poll : PrefixM E Unit)
    (multicast : Nat → Nat → PrefixM E Unit)
    (transmit : Nat → Nat → List Packet → Nat → PrefixM E Int)
    (hr : ∀ msg src, ErasesPrefix (receive msg src) (liftWG (wgReceive msg src)))
    (hp : ErasesPrefix poll Env.pollScheduledInline)
    (hm : ∀ family addr, ErasesPrefix (multicast family addr) (Env.xmitMulticastLoop family addr))
    (hx : ∀ family addr pkts mtu, ErasesPrefix (transmit family addr pkts mtu)
      (liftWG (wgXmit family addr pkts mtu)))
    (d : Device) (cqes : List Int) (item : Env.BatchItem) :
    ErasesPrefix (batchItemWith receive poll multicast transmit d cqes item)
      (Environment.batchItemSource d cqes item) := by
  cases item
  all_goals
    unfold batchItemWith Environment.batchItemSource
    repeat' first
      | (tag_deferred_erase_at atom receive; exact hr _ _)
      | (tag_deferred_erase_at atom poll; exact hp)
      | (tag_deferred_erase_at atom multicast; exact hm _ _)
      | (tag_deferred_erase_at atom transmit; exact hx _ _ _ _)
      | rx_env_traffic_erasure
  all_goals contradiction

theorem batch
    (one : Device → List Int → Env.BatchItem → PrefixM E (ForInStep (List Int)))
    (after : PrefixM E Unit)
    (ho : ∀ d cqes item, ErasesPrefix (one d cqes item) (Environment.batchItemSource d cqes item))
    (ha : ErasesPrefix after Env.afterBatch)
    (items : List Env.BatchItem) :
    ErasesPrefix (TrafficSource.batchWith one after items) (Env.batch items) := by
  rw [← Environment.batchSource_eq]
  unfold TrafficSource.batchWith Environment.batchSource
  repeat' first
    | (tag_deferred_erase_at atom one; exact ho _ _ _)
    | (tag_deferred_erase_at atom after; exact ha)
    | rx_env_traffic_erasure
end Leanux.Proofs.WG.Progress.TrafficErasure
