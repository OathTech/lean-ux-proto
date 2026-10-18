import Leanux.Proofs.WG.Noise.PendingTrafficFrames

namespace Leanux.Proofs.WG.Noise.PendingTraffic
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do
open Lifetimes Queues PendingSession

theorem publish_native (id : SkbId) (state : PacketState) (seen : List Nat) :
    Preserves (fun w => NativeInv w seen) (enqueuePerPeerRx (pure () : WG.M Unit) id state) := by
  rw [PublicationFrontier.enqueuePerPeerRx_factor]
  simp only [pure_bind]
  exact preserves_bind (PendingCrypt.publish_native id state seen)
    (fun pid => peer_keeps (some pid) seen)

theorem consume_native (msg : List UInt8) (src : SkbSource) (ds : Nat) (seen : List Nat) :
    Preserves (fun w => NativeInv w seen) (consumeData msg src ds) := by
  unfold consumeData WG.orM
  simp (config := {zeta := false}) only [branch,invariant,newRxSkb,freeRxSkb]
  repeat' first
    | (rx_retention_head indexLookup; exact index_native _ _ seen)
    | (rx_retention_head keypairGet; exact acquire_native _ seen)
    | (rx_retention_head keypairGetNull; exact PendingReception.native_store _ keypairGetNull_sameStore seen)
    | (rx_retention_head enqueuePerDeviceAndPeerRx; exact enqueue_native _ seen)
    | (rx_retention_head enqueuePerPeerRx; exact publish_native _ _ seen)
    | (rx_retention_head keypairPut; exact keypair_keeps _ _ seen)
    | (rx_retention_head peerPut; exact peer_keeps _ seen)
    | (rx_retention_head liftSkb; exact keeps_packet _ seen)
    | pending_native_step seen

theorem packet_native (msg : List UInt8) (src : SkbSource) (seen : List Nat) :
    Preserves (fun w => NativeInv w seen) (packetReceive msg src) := by
  unfold packetReceive cpumaskNextOnline
  simp (config := {zeta := false}) only [branch,queueDeviceWork,unsupported,invariant]
  repeat' first
    | (rx_retention_head prepareSkbHeader; exact (prepareSkbHeader_sameWGWorld _).wp (fun w => NativeInv w seen))
    | (rx_retention_head ipTunnelGetDsfield; exact (ipTunnelGetDsfield_sameWGWorld _ _).wp (fun w => NativeInv w seen))
    | (rx_retention_head consumeData; exact consume_native _ _ _ seen)
    | pending_native_step seen

theorem receive_native (msg : List UInt8) (src : SkbSource) (seen : List Nat) :
    Preserves (fun w => NativeInv w seen) (wgReceive msg src) := by
  unfold wgReceive
  simp (config := {zeta := false}) only [branch,unsupported]
  repeat' first
    | (rx_retention_head packetReceive; exact packet_native _ _ seen)
    | pending_native_step seen
theorem receive (msg : List UInt8) (src : SkbSource) :
    PrefixPreserves StateInv HistorySafe (RxHistory.mixed (liftWGObserver (wgReceivePrefix msg src))) :=
  lifecycle_observed _ _ (wgReceivePrefix_erases msg src) (receive_native msg src)

theorem drained (what : String) (queues : List Bool) :
    PrefixPreserves StateInv HistorySafe (RxHistory.mixed (requireDrainedPrefix what queues)) :=
  PendingScheduler.mixed_store _ _ (requireDrainedPrefix_erases what queues)
    (PendingScheduler.requireDrained_store what queues)

theorem multicast (family addr : Nat) :
    PrefixPreserves StateInv HistorySafe (RxHistory.audit (xmitMulticastLoopAudit family addr)) :=
  PendingScheduler.audit_store _ _ (xmitMulticastLoopAudit_erases family addr) (multicast_store family addr)

theorem transmit (family addr : Nat) (packets : List Packet) (mtu : Nat) :
    PrefixPreserves StateInv HistorySafe
      (RxHistory.mixed (liftWGObserver (wgXmitPrefix family addr packets mtu))) :=
  lifecycle_observed _ _ (wgXmitPrefix_erases family addr packets mtu)
    (PendingStack.wgXmit_native family addr packets mtu)

theorem inject (workers : PendingScheduler.Workers)
    (family port : Nat) (msg : List UInt8) (tos : Nat) (ll : Bool) (dest : Nat) :
    PrefixPreserves StateInv HistorySafe (RxHistory.inject family port msg tos ll dest) := by
  rw [TrafficSource.inject_factor]
  exact TrafficSource.inject_preserves PendingScheduler.safe state_product_store
    _ _ _ receive (PendingScheduler.crypt workers) drained family port msg tos ll dest

theorem afterBatch (workers : PendingScheduler.Workers) (leaves : PendingScheduler.DeferredLeaves) :
    PrefixPreserves StateInv HistorySafe RxHistory.afterBatch := by
  rw [TrafficSource.afterBatch_factor]
  exact TrafficSource.afterBatch_preserves PendingScheduler.safe state_product_store
    _ _ _ _ _ (PendingScheduler.crypt workers) (PendingScheduler.send workers leaves)
    run_one_send_observed (PendingScheduler.schedule workers) drained

theorem flood (workers : PendingScheduler.Workers) (leaves : PendingScheduler.DeferredLeaves)
    (count port family : Nat) (messages : List (List UInt8)) :
    PrefixPreserves StateInv HistorySafe (RxHistory.flood count port family messages) := by
  rw [TrafficSource.flood_factor]
  exact TrafficSource.flood_preserves PendingScheduler.safe state_product_store
    _ _ _ _ receive actual_napi_inline (afterBatch workers leaves) drained count port family messages

theorem batch_item (device : Device) (cqes : List Int) (item : Env.BatchItem) :
    PrefixPreserves StateInv HistorySafe (RxHistory.batchItem device cqes item) := by
  rw [rxBatchItem_factor]
  exact batchItemWith_preserves PendingScheduler.safe state_store
    _ _ _ _ receive actual_napi_inline multicast transmit device cqes item

theorem batch (workers : PendingScheduler.Workers) (leaves : PendingScheduler.DeferredLeaves)
    (items : List Env.BatchItem) :
    PrefixPreserves StateInv HistorySafe (RxHistory.batch items) := by
  rw [TrafficSource.batch_factor]
  exact TrafficSource.batch_preserves PendingScheduler.safe state_product_store
    _ _ batch_item (afterBatch workers leaves) items

theorem observe (workers : PendingScheduler.Workers) (leaves : PendingScheduler.DeferredLeaves) :
    PrefixPreserves StateInv HistorySafe RxHistory.observe := by
  unfold RxHistory.observe
  exact PrefixPreserves.bind (PendingScheduler.idle workers leaves) (fun _ =>
    viewLiftPrefix_preserves productStoreView PendingScheduler.safe state_product_store observeTail_sameKernel)

theorem handshake_worker (workers : PendingScheduler.Workers) :
    PrefixPreserves StateInv HistorySafe RxHistory.handshakeReceiveWorker := by
  unfold RxHistory.handshakeReceiveWorker
  exact workerLoopPrefix_preserves _ _ PendingScheduler.safe PendingReception.receiveStep
    (PendingScheduler.nested workers .receiveWorker) _ _

end Leanux.Proofs.WG.Noise.PendingTraffic
