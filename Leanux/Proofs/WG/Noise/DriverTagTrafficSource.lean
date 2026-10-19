import Leanux.Proofs.WG.Progress.TrafficErasureSource
import Leanux.Proofs.WG.Noise.DriverTagTrafficFrames

set_option autoImplicit false
namespace Leanux.Proofs.WG.Noise.DriverTags.Traffic
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do
open Lifetimes Queues

theorem acquire_retained (entry : TagMap) (kid : Option KeypairId) :
    Preserves (Silent.Retained entry) (keypairGet kid) :=
  Silent.of_staging entry _ (fun g => Index.keypairGet_staging kid g)

theorem publish_retained (entry : TagMap) (id : SkbId) (state : PacketState) :
    Preserves (Silent.Retained entry) (enqueuePerPeerRx (pure () : WG.M Unit) id state) := by
  rw [PublicationFrontier.enqueuePerPeerRx_factor]
  simp only [pure_bind]
  exact preserves_bind (Silent.of_frame entry _ (Silent.publish_frame id state))
    (fun pid => Silent.peerPut entry (some pid))

theorem consume_retained (entry : TagMap) (msg : List UInt8) (src : SkbSource) (ds : Nat) :
    Preserves (Silent.Retained entry) (consumeData msg src ds) := by
  unfold consumeData WG.orM
  simp (config := {zeta := false}) only [branch,invariant,newRxSkb,freeRxSkb]
  repeat' first
    | (rx_retention_head indexLookup; exact Silent.of_frame entry _ (index_frame _ _))
    | (rx_retention_head keypairGet; exact acquire_retained entry _)
    | (rx_retention_head keypairGetNull; exact Silent.of_frame entry _ (store_frame keypairGetNull_sameStore))
    | (rx_retention_head enqueuePerDeviceAndPeerRx; exact Silent.of_frame entry _ (enqueue_frame _))
    | (rx_retention_head enqueuePerPeerRx; exact publish_retained entry _ _)
    | (rx_retention_head keypairPut; exact Silent.keypairPut entry _ _)
    | (rx_retention_head peerPut; exact Silent.peerPut entry _)
    | (rx_retention_head liftSkb; exact Silent.of_frame entry _ (Silent.packet_frame _))
    | silent_native_step entry

theorem packet_retained (entry : TagMap) (msg : List UInt8) (src : SkbSource) :
    Preserves (Silent.Retained entry) (packetReceive msg src) := by
  unfold packetReceive cpumaskNextOnline
  simp (config := {zeta := false}) only [branch,queueDeviceWork,unsupported,invariant]
  repeat' first
    | (rx_retention_head prepareSkbHeader; exact (prepareSkbHeader_sameWGWorld _).wp (Silent.Retained entry))
    | (rx_retention_head ipTunnelGetDsfield; exact (ipTunnelGetDsfield_sameWGWorld _ _).wp (Silent.Retained entry))
    | (rx_retention_head consumeData; exact consume_retained entry _ _ _)
    | silent_native_step entry

theorem receive_retained (entry : TagMap) (msg : List UInt8) (src : SkbSource) :
    Preserves (Silent.Retained entry) (wgReceive msg src) := by
  unfold wgReceive
  simp (config := {zeta := false}) only [branch,unsupported]
  repeat' first
    | (rx_retention_head packetReceive; exact packet_retained entry _ _)
    | silent_native_step entry


/- Source adapters use the original calls. Receive admission and transmit have
no helper receipt; deferred callers retain their actual completed receipts. -/
def receive (msg : List UInt8) (src : SkbSource) : ProductObs Unit :=
  liftWGObserver (liftWGPrefix (wgReceive msg src))

def transmit (family addr : Nat) (packets : List Packet) (mtu : Nat) : ProductObs Int :=
  liftWGObserver (liftWGPrefix (wgXmit family addr packets mtu))

def multicast (family addr : Nat) : ProductObs Unit :=
  liftPrefix (Env.xmitMulticastLoop family addr)

def drained (what : String) (queues : List Bool) : ProductObs Unit :=
  Scheduled.deferred (.drained what queues)

theorem receive_preserves (entry : TagMap) (msg : List UInt8) (src : SkbSource) :
    PrefixPreserves (StateInv entry) ValidHistory (receive msg src) :=
  Scheduler.native_observed entry _ (Silent.lift_preserves entry _ (fun initial => receive_retained initial msg src))

theorem transmit_preserves (entry : TagMap) (family addr : Nat) (packets : List Packet) (mtu : Nat) :
    PrefixPreserves (StateInv entry) ValidHistory (transmit family addr packets mtu) :=
  Scheduler.native_observed entry _ (Silent.lift_preserves entry _ (fun initial => Transmit.native initial family addr packets mtu))

theorem multicast_preserves (entry : TagMap) (family addr : Nat) :
    PrefixPreserves (StateInv entry) ValidHistory (multicast family addr) :=
  lift_product_store entry _ (PendingTraffic.multicast_store family addr)

theorem drained_preserves (entry : TagMap) (what : String) (queues : List Bool) :
    PrefixPreserves (StateInv entry) ValidHistory (drained what queues) :=
  Scheduled.deferred_preserves entry (.drained what queues)

theorem receive_erases (msg : List UInt8) (src : SkbSource) :
    ErasesPrefix (receive msg src) (liftWG (wgReceive msg src)) :=
  liftWGObserver_erases (erasesStatePrefix_lift _)

theorem transmit_erases (family addr : Nat) (packets : List Packet) (mtu : Nat) :
    ErasesPrefix (transmit family addr packets mtu) (liftWG (wgXmit family addr packets mtu)) :=
  liftWGObserver_erases (erasesStatePrefix_lift _)

theorem multicast_erases (family addr : Nat) :
    ErasesPrefix (multicast family addr) (Env.xmitMulticastLoop family addr) :=
  erasesPrefix_lift _

theorem drained_erases (what : String) (queues : List Bool) :
    ErasesPrefix (drained what queues) (Env.requireDrained what queues) :=
  Scheduled.deferred_erases (.drained what queues)

def inject (family port : Nat) (msg : List UInt8) (tos : Nat := 0)
    (ll : Bool := false) (dest : Nat := 0) : ProductObs Int :=
  TrafficSource.injectWith receive (Scheduled.deferred .crypt) drained family port msg tos ll dest

def afterBatch : ProductObs Unit :=
  TrafficSource.afterBatchWith (Scheduled.deferred .crypt) (Scheduled.deferred .sendAll)
    (Scheduled.deferred .sendOne) (fun stack => Scheduled.schedule stack) drained

def flood (count port family : Nat) (messages : List (List UInt8)) : ProductObs Int :=
  TrafficSource.floodWith receive Scheduled.inlinePoll afterBatch drained count port family messages

def batchItem (device : Device) (cqes : List Int) (item : Env.BatchItem) :
    ProductObs (ForInStep (List Int)) :=
  batchItemWith receive Scheduled.inlinePoll multicast transmit device cqes item

def batch (items : List Env.BatchItem) : ProductObs Int :=
  TrafficSource.batchWith batchItem afterBatch items

theorem inject_preserves (entry : TagMap) (family port : Nat) (msg : List UInt8)
    (tos : Nat) (ll : Bool) (dest : Nat) :
    PrefixPreserves (StateInv entry) ValidHistory (inject family port msg tos ll dest) :=
  TrafficSource.inject_preserves (safe entry) (state_product_store entry) _ _ _
    (receive_preserves entry) (Scheduled.deferred_preserves entry .crypt)
    (drained_preserves entry) family port msg tos ll dest

theorem afterBatch_preserves (entry : TagMap) :
    PrefixPreserves (StateInv entry) ValidHistory afterBatch :=
  TrafficSource.afterBatch_preserves (safe entry) (state_product_store entry) _ _ _ _ _
    (Scheduled.deferred_preserves entry .crypt) (Scheduled.deferred_preserves entry .sendAll)
    (Scheduled.deferred_preserves entry .sendOne) (Scheduled.schedule_preserves entry)
    (drained_preserves entry)

theorem flood_preserves (entry : TagMap) (count port family : Nat) (messages : List (List UInt8)) :
    PrefixPreserves (StateInv entry) ValidHistory (flood count port family messages) :=
  TrafficSource.flood_preserves (safe entry) (state_product_store entry) _ _ _ _
    (receive_preserves entry) (Scheduled.inlinePoll_preserves entry) (afterBatch_preserves entry)
    (drained_preserves entry) count port family messages

theorem batchItem_preserves (entry : TagMap) (device : Device) (cqes : List Int) (item : Env.BatchItem) :
    PrefixPreserves (StateInv entry) ValidHistory (batchItem device cqes item) :=
  batchItemWith_preserves (safe entry) (state_store entry) _ _ _ _
    (receive_preserves entry) (Scheduled.inlinePoll_preserves entry) (multicast_preserves entry)
    (transmit_preserves entry) device cqes item

theorem batch_preserves (entry : TagMap) (items : List Env.BatchItem) :
    PrefixPreserves (StateInv entry) ValidHistory (batch items) :=
  TrafficSource.batch_preserves (safe entry) (state_product_store entry) _ _
    (batchItem_preserves entry) (afterBatch_preserves entry) items



theorem inject_erases (family port : Nat) (msg : List UInt8) (tos : Nat) (ll : Bool) (dest : Nat) :
    ErasesPrefix (inject family port msg tos ll dest) (Env.inject family port msg tos ll dest) :=
  Progress.TrafficErasure.inject _ _ _ receive_erases (Scheduled.deferred_erases .crypt)
    drained_erases family port msg tos ll dest

theorem afterBatch_erases : ErasesPrefix afterBatch Env.afterBatch :=
  Progress.TrafficErasure.afterBatch _ _ _ _ _ (Scheduled.deferred_erases .crypt)
    (Scheduled.deferred_erases .sendAll) (Scheduled.deferred_erases .sendOne)
    Scheduled.schedule_erases drained_erases

theorem flood_erases (count port family : Nat) (messages : List (List UInt8)) :
    ErasesPrefix (flood count port family messages) (Env.flood count port family messages) :=
  Progress.TrafficErasure.flood _ _ _ _ receive_erases (erasesPrefix_lift _)
    afterBatch_erases drained_erases count port family messages

theorem batchItem_erases (device : Device) (cqes : List Int) (item : Env.BatchItem) :
    ErasesPrefix (batchItem device cqes item) (Environment.batchItemSource device cqes item) :=
  Progress.TrafficErasure.batchItem _ _ _ _ receive_erases (erasesPrefix_lift _)
    multicast_erases transmit_erases device cqes item

theorem batch_erases (items : List Env.BatchItem) : ErasesPrefix (batch items) (Env.batch items) :=
  Progress.TrafficErasure.batch _ _ batchItem_erases afterBatch_erases items

def observe : ProductObs (Int × Lean.Json) := do
  Scheduled.deferred .idle
  liftPrefix Environment.observeTail

theorem observe_preserves (entry : TagMap) :
    PrefixPreserves (StateInv entry) ValidHistory observe :=
  PrefixPreserves.bind (Scheduled.deferred_preserves entry .idle) (fun _ =>
    lift_product_store entry _ observeTail_sameKernel)

theorem observe_erases : ErasesPrefix observe Env.observe := by
  rw [Environment.observe_eq]
  exact erasesPrefix_bind (Scheduled.deferred_erases .idle) (fun _ => erasesPrefix_lift _)

def handshakeWorker : ProductObs Unit :=
  workerLoopPrefix .receiveWorker none (liftWGObserver receiveStepCompleted)
    (Scheduled.nested .receiveWorker) (MAX_QUEUED_INCOMING_HANDSHAKES + 1)
    "the handshake queue did not drain"

theorem handshakeWorker_preserves (entry : TagMap) :
    PrefixPreserves (StateInv entry) ValidHistory handshakeWorker :=
  workerLoopPrefix_preserves _ _ (safe entry)
    (Scheduler.native_observed entry _ (receiveStepCompleted_preserves entry))
    (Scheduled.nested_preserves entry .receiveWorker) _ _

theorem handshakeWorker_erases :
    ErasesPrefix handshakeWorker (WG.handshakeReceiveWorker (Env.nestedResched .receiveWorker)) :=
  workerLoopPrefix_erases _ _ (liftWGObserver_erases receiveStepCompleted_erases)
    (Scheduled.nested_erases .receiveWorker) _ _

end Leanux.Proofs.WG.Noise.DriverTags.Traffic
