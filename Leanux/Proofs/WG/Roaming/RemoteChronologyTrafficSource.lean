import Leanux.Proofs.WG.Roaming.RemoteChronologyDeferredSource
import Leanux.Proofs.WG.Roaming.RemoteDriverTrafficSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Roaming.RemoteChronology.Driver
open Leanux Leanux.WG Noise Lifetimes Queues Std.Do
open Leanux.Proofs.Framing Leanux.Proofs.Logged
open Leanux.Proofs.WG.Configuration

namespace Traffic
theorem receive_preserves (entry : RemoteMap) (msg : List UInt8) (src : SkbSource) :
    PrefixPreserves (Inv entry) RemoteDriver.Safe (RemoteDriver.Traffic.receive msg src) :=
  mixed_native entry _ _ (wgReceivePrefix_erases msg src)
    (fun before => RemoteSilent.of_frame before _ (RemoteDriver.Traffic.receive_frame msg src))

theorem transmit_preserves (entry : RemoteMap) (family addr : Nat)
    (packets : List Packet) (mtu : Nat) :
    PrefixPreserves (Inv entry) RemoteDriver.Safe (RemoteDriver.Traffic.transmit family addr packets mtu) :=
  mixed_native entry _ _ (wgXmitPrefix_erases family addr packets mtu)
    (fun before => (ensures_iff _ _ _).mpr (RemotePoll.xmit_retained before family addr packets mtu))

theorem multicast_preserves (entry : RemoteMap) (family addr : Nat) :
    PrefixPreserves (Inv entry) RemoteDriver.Safe (RemoteDriver.Traffic.multicast family addr) :=
  audit_store entry _ _ (xmitMulticastLoopAudit_erases family addr) (PendingTraffic.multicast_store family addr)

theorem drained_preserves (entry : RemoteMap) (what : String) (flags : List Bool) :
    PrefixPreserves (Inv entry) RemoteDriver.Safe (RemoteDriver.Traffic.drained what flags) :=
  mixed_store entry _ _ (requireDrainedPrefix_erases what flags) (PendingScheduler.requireDrained_store what flags)

theorem inlinePoll_preserves (entry : RemoteMap) :
    PrefixPreserves (Inv entry) RemoteDriver.Safe RemoteDriver.Traffic.inlinePoll :=
  focus_relative entry _ Poll.inline_relative

theorem inject_preserves (entry : RemoteMap) (family port : Nat) (msg : List UInt8)
    (tos : Nat) (ll : Bool) (dest : Nat) :
    PrefixPreserves (Inv entry) RemoteDriver.Safe (RemoteDriver.Traffic.inject family port msg tos ll dest) :=
  TrafficSource.inject_preserves (safe entry) (store_inv entry) _ _ _
    (receive_preserves entry) (Deferred.crypt_preserves entry) (drained_preserves entry)
    family port msg tos ll dest

theorem afterBatch_preserves (entry : RemoteMap) :
    PrefixPreserves (Inv entry) RemoteDriver.Safe RemoteDriver.Traffic.afterBatch :=
  TrafficSource.afterBatch_preserves (safe entry) (store_inv entry) _ _ _ _ _
    (Deferred.crypt_preserves entry) (Deferred.send_preserves entry) (Deferred.sendOne_preserves entry)
    (Scheduler.schedule_preserves entry) (drained_preserves entry)

theorem flood_preserves (entry : RemoteMap) (count port family : Nat)
    (messages : List (List UInt8)) :
    PrefixPreserves (Inv entry) RemoteDriver.Safe (RemoteDriver.Traffic.flood count port family messages) :=
  TrafficSource.flood_preserves (safe entry) (store_inv entry) _ _ _ _
    (receive_preserves entry) (inlinePoll_preserves entry) (afterBatch_preserves entry)
    (drained_preserves entry) count port family messages

theorem batchItem_preserves (entry : RemoteMap) (d : Device) (cqes : List Int) (item : Env.BatchItem) :
    PrefixPreserves (Inv entry) RemoteDriver.Safe (RemoteDriver.Traffic.batchItem d cqes item) :=
  batchItemWith_preserves (safe entry) (wg_store_inv entry) _ _ _ _
    (receive_preserves entry) (inlinePoll_preserves entry) (multicast_preserves entry)
    (transmit_preserves entry) d cqes item

theorem batch_preserves (entry : RemoteMap) (items : List Env.BatchItem) :
    PrefixPreserves (Inv entry) RemoteDriver.Safe (RemoteDriver.Traffic.batch items) :=
  TrafficSource.batch_preserves (safe entry) (store_inv entry) _ _
    (batchItem_preserves entry) (afterBatch_preserves entry) items
end Traffic

end Leanux.Proofs.WG.Roaming.RemoteChronology.Driver
