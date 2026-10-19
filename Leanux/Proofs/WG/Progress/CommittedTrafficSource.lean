import Leanux.Proofs.WG.Progress.CommittedDeferredSource
import Leanux.Proofs.WG.Progress.TrafficErasureSource

/-! Actual traffic callers route every deferred scheduler continuation through
CommittedRuns; scheduler-free native leaves retain the original behavior. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.CommittedRuns.Traffic
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues

/- Only original scheduler-free admission, transmission, inline NAPI and guards
are lifted. The actual deferred scheduler callbacks retain the journal. -/
def receive (msg : List UInt8) (src : SkbSource) : PrefixM Receipt Unit :=
  liftPrefix (liftWG (wgReceive msg src))
def transmit (family addr : Nat) (packets : List Packet) (mtu : Nat) : PrefixM Receipt Int :=
  liftPrefix (liftWG (wgXmit family addr packets mtu))
def multicast (family addr : Nat) : PrefixM Receipt Unit :=
  liftPrefix (Env.xmitMulticastLoop family addr)
def drained (what : String) (queues : List Bool) : PrefixM Receipt Unit :=
  liftPrefix (Env.requireDrained what queues)
def inlinePoll : PrefixM Receipt Unit := liftPrefix Env.pollScheduledInline

def inject (family port : Nat) (msg : List UInt8) (tos : Nat) (ll : Bool) (dest : Nat) :
    PrefixM Receipt Int :=
  TrafficSource.injectWith receive Deferred.crypt drained family port msg tos ll dest
def afterBatch : PrefixM Receipt Unit :=
  TrafficSource.afterBatchWith Deferred.crypt Deferred.send (Deferred.deferred .sendOne)
    (fun stack=>CommittedRuns.schedule stack) drained
def flood (count port family : Nat) (messages : List (List UInt8)) : PrefixM Receipt Int :=
  TrafficSource.floodWith receive inlinePoll afterBatch drained count port family messages
def batchItem (device : Device) (cqes : List Int) (item : Env.BatchItem) :
    PrefixM Receipt (ForInStep (List Int)) :=
  batchItemWith receive inlinePoll multicast transmit device cqes item
def batch (items : List Env.BatchItem) : PrefixM Receipt Int :=
  TrafficSource.batchWith batchItem afterBatch items
def observe : PrefixM Receipt (Int × Lean.Json) := do
  Deferred.idle
  liftPrefix Environment.observeTail

theorem inject_preserves (family port : Nat) (msg : List UInt8) (tos : Nat) (ll : Bool) (dest : Nat) :
    PrefixPreserves (fun h _=>ValidHistory h) ValidHistory (inject family port msg tos ll dest) :=
  TrafficSource.inject_preserves (I := fun h _=>ValidHistory h) (S := ValidHistory)
    (fun _ _ h=>h) (fun _ _ _ _ h=>h) _ _ _
    (fun _ _=>lift_preserves _) Deferred.crypt_preserves (fun _ _=>lift_preserves _)
    family port msg tos ll dest

theorem afterBatch_preserves :
    PrefixPreserves (fun h _=>ValidHistory h) ValidHistory afterBatch :=
  TrafficSource.afterBatch_preserves (I := fun h _=>ValidHistory h) (S := ValidHistory)
    (fun _ _ h=>h) (fun _ _ _ _ h=>h) _ _ _ _ _
    Deferred.crypt_preserves Deferred.send_preserves (Deferred.deferred_preserves .sendOne)
    CommittedRuns.schedule_preserves (fun _ _=>lift_preserves _)

theorem flood_preserves (count port family : Nat) (messages : List (List UInt8)) :
    PrefixPreserves (fun h _=>ValidHistory h) ValidHistory (flood count port family messages) :=
  TrafficSource.flood_preserves (I := fun h _=>ValidHistory h) (S := ValidHistory)
    (fun _ _ h=>h) (fun _ _ _ _ h=>h) _ _ _ _
    (fun _ _=>lift_preserves _) (lift_preserves _) afterBatch_preserves
    (fun _ _=>lift_preserves _) count port family messages

theorem batchItem_preserves (device : Device) (cqes : List Int) (item : Env.BatchItem) :
    PrefixPreserves (fun h _=>ValidHistory h) ValidHistory (batchItem device cqes item) :=
  batchItemWith_preserves (I := fun h _=>ValidHistory h) (S := ValidHistory)
    (fun _ _ h=>h) (fun _ _ _ _ h=>h) _ _ _ _
    (fun _ _=>lift_preserves _) (lift_preserves _) (fun _ _=>lift_preserves _)
    (fun _ _ _ _=>lift_preserves _) device cqes item

theorem batch_preserves (items : List Env.BatchItem) :
    PrefixPreserves (fun h _=>ValidHistory h) ValidHistory (batch items) :=
  TrafficSource.batch_preserves (I := fun h _=>ValidHistory h) (S := ValidHistory)
    (fun _ _ h=>h) (fun _ _ _ _ h=>h) _ _ batchItem_preserves afterBatch_preserves items

theorem observe_preserves :
    PrefixPreserves (fun h _=>ValidHistory h) ValidHistory observe :=
  PrefixPreserves.bind Deferred.idle_preserves (fun _=>lift_preserves _)

theorem inject_erases (family port : Nat) (msg : List UInt8) (tos : Nat) (ll : Bool) (dest : Nat) :
    ErasesPrefix (inject family port msg tos ll dest) (Env.inject family port msg tos ll dest) :=
  TrafficErasure.inject _ _ _ (fun _ _=>erasesPrefix_lift _) Deferred.crypt_erases
    (fun _ _=>erasesPrefix_lift _) family port msg tos ll dest
theorem afterBatch_erases : ErasesPrefix afterBatch Env.afterBatch :=
  TrafficErasure.afterBatch _ _ _ _ _ Deferred.crypt_erases Deferred.send_erases
    (Deferred.deferred_erases .sendOne) CommittedRuns.schedule_erases (fun _ _=>erasesPrefix_lift _)
theorem flood_erases (count port family : Nat) (messages : List (List UInt8)) :
    ErasesPrefix (flood count port family messages) (Env.flood count port family messages) :=
  TrafficErasure.flood _ _ _ _ (fun _ _=>erasesPrefix_lift _) (erasesPrefix_lift _)
    afterBatch_erases (fun _ _=>erasesPrefix_lift _) count port family messages
theorem batchItem_erases (device : Device) (cqes : List Int) (item : Env.BatchItem) :
    ErasesPrefix (batchItem device cqes item) (Environment.batchItemSource device cqes item) :=
  TrafficErasure.batchItem _ _ _ _ (fun _ _=>erasesPrefix_lift _) (erasesPrefix_lift _)
    (fun _ _=>erasesPrefix_lift _) (fun _ _ _ _=>erasesPrefix_lift _) device cqes item
theorem batch_erases (items : List Env.BatchItem) : ErasesPrefix (batch items) (Env.batch items) :=
  TrafficErasure.batch _ _ batchItem_erases afterBatch_erases items
theorem observe_erases : ErasesPrefix observe Env.observe := by
  rw [Environment.observe_eq]
  exact erasesPrefix_bind Deferred.idle_erases (fun _=>erasesPrefix_lift _)

end Leanux.Proofs.WG.Progress.CommittedRuns.Traffic
