import Leanux.Proofs.WG.Roaming.PollAuthenticationDeferredSource
import Leanux.Proofs.WG.Packets.PublicationTraffic
import Leanux.Proofs.WG.Lifetimes.TrafficPreservation
import Leanux.Proofs.WG.Lifetimes.BatchItemSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Roaming.PollAuthentication.Traffic
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do
open Queues Lifetimes

theorem receive (msg : List UInt8) (src : SkbSource) :
    PrefixPreserves Reached PublicSafe (RxHistory.mixed (liftWGObserver (wgReceivePrefix msg src))) :=
  mixed _
    ((pinned_const _private.Leanux.Proofs.WG.Packets.PublicationTraffic.«0».Leanux.Proofs.WG.PublicationTraffic.receive) msg src)

theorem transmit (family addr : Nat) (packets : List Packet) (mtu : Nat) :
    PrefixPreserves Reached PublicSafe
      (RxHistory.mixed (liftWGObserver (wgXmitPrefix family addr packets mtu))) :=
  mixed _
    ((pinned_const _private.Leanux.Proofs.WG.Packets.PublicationTraffic.«0».Leanux.Proofs.WG.PublicationTraffic.transmit) family addr packets mtu)

theorem multicast (family addr : Nat) :
    PrefixPreserves Reached PublicSafe (RxHistory.audit (xmitMulticastLoopAudit family addr)) :=
  audit _
    ((pinned_const _private.Leanux.Proofs.WG.Packets.PublicationTraffic.«0».Leanux.Proofs.WG.PublicationTraffic.multicast) family addr)

theorem handshakeReceiveWorker :
    PrefixPreserves Reached PublicSafe RxHistory.handshakeReceiveWorker :=
  workerLoopPrefix_preserves _ _ reached_safe receiveStep (nestedResched _) _ _

theorem inject (family port : Nat) (msg : List UInt8) (tos : Nat) (ll : Bool) (dest : Nat) :
    PrefixPreserves Reached PublicSafe (RxHistory.inject family port msg tos ll dest) := by
  rw [TrafficSource.inject_factor]
  exact TrafficSource.inject_preserves reached_safe reached_store _ _ _
    receive Deferred.crypt Deferred.drained family port msg tos ll dest

theorem afterBatch : PrefixPreserves Reached PublicSafe RxHistory.afterBatch := by
  rw [TrafficSource.afterBatch_factor]
  exact TrafficSource.afterBatch_preserves reached_safe reached_store _ _ _ _ _
    Deferred.crypt Deferred.send Deferred.sendOne schedule Deferred.drained

theorem flood (count port family : Nat) (messages : List (List UInt8)) :
    PrefixPreserves Reached PublicSafe (RxHistory.flood count port family messages) := by
  rw [TrafficSource.flood_factor]
  exact TrafficSource.flood_preserves reached_safe reached_store _ _ _ _
    receive pollScheduledInline afterBatch Deferred.drained count port family messages

theorem batchItem (d : Device) (cqes : List Int) (item : Env.BatchItem) :
    PrefixPreserves Reached PublicSafe (RxHistory.batchItem d cqes item) := by
  rw [rxBatchItem_factor]
  exact batchItemWith_preserves reached_safe reached_wgStore _ _ _ _
    receive pollScheduledInline multicast transmit d cqes item

theorem batch (items : List Env.BatchItem) :
    PrefixPreserves Reached PublicSafe (RxHistory.batch items) := by
  rw [TrafficSource.batch_factor]
  exact TrafficSource.batch_preserves reached_safe reached_store _ _ batchItem afterBatch items

theorem observe : PrefixPreserves Reached PublicSafe RxHistory.observe :=
  Deferred.idle.bind (fun _ => quiet_store _ observeTail_sameKernel)

end Leanux.Proofs.WG.Roaming.PollAuthentication.Traffic
