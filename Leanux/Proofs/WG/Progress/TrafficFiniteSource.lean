import Leanux.Proofs.WG.Progress.TrafficErasureSource
import Leanux.Proofs.WG.Progress.DeferredFiniteOuterSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.TrafficFinite
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues

/- The admission, transmit, multicast and inline-NAPI leaves are bounded
packet/list computations. Their concrete static allocation reductions are
in PacketAllocationFiniteSource, also used by ActivationFinite. They never
execute the nonstructural handshake creator; queued reception goes through
the finite scheduler in DeferredFinite. -/
def receive (msg : List UInt8) (src : SkbSource) : PrefixM PUnit Unit :=
  liftPrefix (liftWG (wgReceive msg src))
def transmit (family addr : Nat) (packets : List Packet) (mtu : Nat) : PrefixM PUnit Int :=
  liftPrefix (liftWG (wgXmit family addr packets mtu))
def multicast (family addr : Nat) : PrefixM PUnit Unit :=
  liftPrefix (Env.xmitMulticastLoop family addr)
def drained (what : String) (queues : List Bool) : PrefixM PUnit Unit :=
  liftPrefix (Env.requireDrained what queues)
def inlinePoll : PrefixM PUnit Unit := liftPrefix Env.pollScheduledInline
def schedule (stack : Option Worker) : PrefixM PUnit Unit :=
  liftPrefix (SchedulerFinite.schedule stack)

theorem schedule_erases (stack : Option Worker) :
    ErasesPrefix (schedule stack) (Env.schedule stack) := by
  unfold schedule
  rw [SchedulerFinite.schedule_source]
  exact erasesPrefix_lift _

def inject (family port : Nat) (msg : List UInt8) (tos : Nat) (ll : Bool) (dest : Nat) :
    PrefixM PUnit Int :=
  TrafficSource.injectWith receive DeferredFinite.crypt drained family port msg tos ll dest
def afterBatch : PrefixM PUnit Unit :=
  TrafficSource.afterBatchWith DeferredFinite.crypt DeferredFinite.sendAll
    (liftPrefix DeferredFinite.sendOne) schedule drained
def flood (count port family : Nat) (messages : List (List UInt8)) : PrefixM PUnit Int :=
  TrafficSource.floodWith receive inlinePoll afterBatch drained count port family messages
def batchItem (device : Device) (cqes : List Int) (item : Env.BatchItem) :
    PrefixM PUnit (ForInStep (List Int)) :=
  batchItemWith receive inlinePoll multicast transmit device cqes item
def batch (items : List Env.BatchItem) : PrefixM PUnit Int :=
  TrafficSource.batchWith batchItem afterBatch items

theorem inject_erases (family port : Nat) (msg : List UInt8) (tos : Nat) (ll : Bool) (dest : Nat) :
    ErasesPrefix (inject family port msg tos ll dest) (Env.inject family port msg tos ll dest) :=
  TrafficErasure.inject receive DeferredFinite.crypt drained
    (fun _ _ => erasesPrefix_lift _) DeferredFinite.crypt_erases
    (fun _ _ => erasesPrefix_lift _) family port msg tos ll dest

theorem afterBatch_erases : ErasesPrefix afterBatch Env.afterBatch :=
  TrafficErasure.afterBatch DeferredFinite.crypt DeferredFinite.sendAll
    (liftPrefix DeferredFinite.sendOne) schedule drained
    DeferredFinite.crypt_erases DeferredFinite.sendAll_erases
    (by rw [DeferredFinite.sendOne_source]; exact erasesPrefix_lift _)
    schedule_erases (fun _ _ => erasesPrefix_lift _)

theorem flood_erases (count port family : Nat) (messages : List (List UInt8)) :
    ErasesPrefix (flood count port family messages) (Env.flood count port family messages) :=
  TrafficErasure.flood receive inlinePoll afterBatch drained
    (fun _ _ => erasesPrefix_lift _) (erasesPrefix_lift _) afterBatch_erases
    (fun _ _ => erasesPrefix_lift _) count port family messages

theorem batchItem_erases (device : Device) (cqes : List Int) (item : Env.BatchItem) :
    ErasesPrefix (batchItem device cqes item) (Environment.batchItemSource device cqes item) :=
  TrafficErasure.batchItem receive inlinePoll multicast transmit
    (fun _ _ => erasesPrefix_lift _) (erasesPrefix_lift _)
    (fun _ _ => erasesPrefix_lift _) (fun _ _ _ _ => erasesPrefix_lift _) device cqes item

theorem batch_erases (items : List Env.BatchItem) :
    ErasesPrefix (batch items) (Env.batch items) :=
  TrafficErasure.batch batchItem afterBatch batchItem_erases afterBatch_erases items

def nativeInject (family port : Nat) (msg : List UInt8) (tos : Nat) (ll : Bool) (dest : Nat) :
    Leanux.M Int := fun w => (runPrefix (inject family port msg tos ll dest) w []).1
def nativeAfterBatch : Leanux.M Unit := fun w => (runPrefix afterBatch w []).1
def nativeFlood (count port family : Nat) (messages : List (List UInt8)) : Leanux.M Int :=
  fun w => (runPrefix (flood count port family messages) w []).1
def nativeBatch (items : List Env.BatchItem) : Leanux.M Int :=
  fun w => (runPrefix (batch items) w []).1

theorem nativeInject_source (family port : Nat) (msg : List UInt8) (tos : Nat) (ll : Bool) (dest : Nat) :
    Env.inject family port msg tos ll dest = nativeInject family port msg tos ll dest := by
  funext w
  exact (inject_erases family port msg tos ll dest w []).symm

theorem nativeAfterBatch_source : Env.afterBatch = nativeAfterBatch := by
  funext w
  exact (afterBatch_erases w []).symm

theorem nativeFlood_source (count port family : Nat) (messages : List (List UInt8)) :
    Env.flood count port family messages = nativeFlood count port family messages := by
  funext w
  exact (flood_erases count port family messages w []).symm

theorem nativeBatch_source (items : List Env.BatchItem) : Env.batch items = nativeBatch items := by
  funext w
  exact (batch_erases items w []).symm

end Leanux.Proofs.WG.Progress.TrafficFinite
