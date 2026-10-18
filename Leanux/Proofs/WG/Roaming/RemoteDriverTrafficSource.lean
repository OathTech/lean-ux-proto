import Leanux.Proofs.WG.Roaming.RemoteDriverTrafficFrames

set_option autoImplicit false
namespace Leanux.Proofs.WG.Roaming.RemoteDriver
open Leanux Leanux.WG Noise Queues Lifetimes Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do

namespace Traffic

def receive (msg : List UInt8) (src : SkbSource) : PrefixM Event Unit :=
  focus (RxHistory.mixed (liftWGObserver (wgReceivePrefix msg src)))

def transmit (family addr : Nat) (packets : List Packet) (mtu : Nat) : PrefixM Event Int :=
  focus (RxHistory.mixed (liftWGObserver (wgXmitPrefix family addr packets mtu)))

def multicast (family addr : Nat) : PrefixM Event Unit :=
  focus (RxHistory.audit (xmitMulticastLoopAudit family addr))

def drained (what : String) (flags : List Bool) : PrefixM Event Unit :=
  focus (RxHistory.mixed (requireDrainedPrefix what flags))

def inlinePoll : PrefixM Event Unit := focus RxHistory.pollScheduledInline

theorem receive_preserves (entry : RemoteMap) (msg : List UInt8) (src : SkbSource) :
    PrefixPreserves (Inv entry) Safe (receive msg src) :=
  focus_native entry _ _ (Appends.focus _ _ _)
    (RxHistory.mixed_erases (liftWGObserver_erases (wgReceivePrefix_erases msg src)))
    (fun before => RemoteSilent.of_frame before _ (receive_frame msg src))

theorem transmit_preserves (entry : RemoteMap) (family addr : Nat)
    (packets : List Packet) (mtu : Nat) :
    PrefixPreserves (Inv entry) Safe (transmit family addr packets mtu) :=
  focus_native entry _ _ (Appends.focus _ _ _)
    (RxHistory.mixed_erases (liftWGObserver_erases (wgXmitPrefix_erases family addr packets mtu)))
    (fun before => (ensures_iff _ _ _).mpr (RemotePoll.xmit_retained before family addr packets mtu))

theorem multicast_preserves (entry : RemoteMap) (family addr : Nat) :
    PrefixPreserves (Inv entry) Safe (multicast family addr) :=
  focus_store entry _ _ (Appends.focus _ _ _)
    (RxHistory.audit_erases (xmitMulticastLoopAudit_erases family addr))
    (PendingTraffic.multicast_store family addr)

theorem drained_preserves (entry : RemoteMap) (what : String) (flags : List Bool) :
    PrefixPreserves (Inv entry) Safe (drained what flags) :=
  focus_store entry _ _ (Appends.focus _ _ _)
    (RxHistory.mixed_erases (requireDrainedPrefix_erases what flags))
    (PendingScheduler.requireDrained_store what flags)

theorem inlinePoll_preserves (entry : RemoteMap) :
    PrefixPreserves (Inv entry) Safe inlinePoll :=
  covered_focus entry _ RxHistory.pollScheduledInline_appends RemotePoll.inline_covered

theorem receive_projects (msg : List UInt8) (src : SkbSource) :
    ProjectsPrefix rxEvent id (receive msg src)
      (RxHistory.mixed (liftWGObserver (wgReceivePrefix msg src))) :=
  (Appends.focus _ _ _).project_focus Event.rx rxEvent (fun _ => rfl)

theorem transmit_projects (family addr : Nat) (packets : List Packet) (mtu : Nat) :
    ProjectsPrefix rxEvent id (transmit family addr packets mtu)
      (RxHistory.mixed (liftWGObserver (wgXmitPrefix family addr packets mtu))) :=
  (Appends.focus _ _ _).project_focus Event.rx rxEvent (fun _ => rfl)

theorem multicast_projects (family addr : Nat) :
    ProjectsPrefix rxEvent id (multicast family addr)
      (RxHistory.audit (xmitMulticastLoopAudit family addr)) :=
  (Appends.focus _ _ _).project_focus Event.rx rxEvent (fun _ => rfl)

theorem drained_projects (what : String) (flags : List Bool) :
    ProjectsPrefix rxEvent id (drained what flags)
      (RxHistory.mixed (requireDrainedPrefix what flags)) :=
  (Appends.focus _ _ _).project_focus Event.rx rxEvent (fun _ => rfl)

theorem inlinePoll_projects :
    ProjectsPrefix rxEvent id inlinePoll RxHistory.pollScheduledInline :=
  RxHistory.pollScheduledInline_appends.project_focus Event.rx rxEvent (fun _ => rfl)

theorem receive_appends (msg : List UInt8) (src : SkbSource) : Appends (receive msg src) :=
  Appends.focus _ _ _
theorem transmit_appends (family addr : Nat) (packets : List Packet) (mtu : Nat) :
    Appends (transmit family addr packets mtu) := Appends.focus _ _ _
theorem multicast_appends (family addr : Nat) : Appends (multicast family addr) := Appends.focus _ _ _
theorem drained_appends (what : String) (flags : List Bool) : Appends (drained what flags) :=
  Appends.focus _ _ _
theorem inlinePoll_appends : Appends inlinePoll := Appends.focus _ _ _

end Traffic
end Leanux.Proofs.WG.Roaming.RemoteDriver

namespace Leanux.Proofs.WG.Roaming.RemoteDriver.Traffic
open Leanux Leanux.WG Noise Queues Lifetimes Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do

def inject (family port : Nat) (msg : List UInt8) (tos : Nat) (ll : Bool) (dest : Nat) :
    PrefixM Event Int :=
  TrafficSource.injectWith receive Deferred.crypt drained family port msg tos ll dest

def afterBatch : PrefixM Event Unit :=
  TrafficSource.afterBatchWith Deferred.crypt Deferred.send Deferred.sendOne
    (fun stack => Scheduler.schedule stack) drained

def flood (count port family : Nat) (messages : List (List UInt8)) : PrefixM Event Int :=
  TrafficSource.floodWith receive inlinePoll afterBatch drained count port family messages

def batchItem (d : Device) (cqes : List Int) (item : Env.BatchItem) :
    PrefixM Event (ForInStep (List Int)) :=
  batchItemWith receive inlinePoll multicast transmit d cqes item

def batch (items : List Env.BatchItem) : PrefixM Event Int :=
  TrafficSource.batchWith batchItem afterBatch items

theorem inject_projects (family port : Nat) (msg : List UInt8)
    (tos : Nat) (ll : Bool) (dest : Nat) :
    ProjectsPrefix rxEvent id (inject family port msg tos ll dest)
      (RxHistory.inject family port msg tos ll dest) := by
  rw [TrafficSource.inject_factor]
  exact TrafficSource.inject_projects rxEvent _ _ _ _ _ _
    receive_projects Deferred.crypt_projects drained_projects family port msg tos ll dest

theorem afterBatch_projects :
    ProjectsPrefix rxEvent id afterBatch RxHistory.afterBatch := by
  rw [TrafficSource.afterBatch_factor]
  exact TrafficSource.afterBatch_projects rxEvent _ _ _ _ _ _ _ _ _ _
    Deferred.crypt_projects Deferred.send_projects Deferred.sendOne_projects
    Scheduler.schedule_projects drained_projects

theorem flood_projects (count port family : Nat) (messages : List (List UInt8)) :
    ProjectsPrefix rxEvent id (flood count port family messages)
      (RxHistory.flood count port family messages) := by
  rw [TrafficSource.flood_factor]
  exact TrafficSource.flood_projects rxEvent _ _ _ _ _ _ _ _
    receive_projects inlinePoll_projects afterBatch_projects drained_projects count port family messages

theorem batchItem_projects (d : Device) (cqes : List Int) (item : Env.BatchItem) :
    ProjectsPrefix rxEvent id (batchItem d cqes item) (RxHistory.batchItem d cqes item) := by
  rw [rxBatchItem_factor]
  exact batchItemWith_projects rxEvent _ _ _ _ _ _ _ _ receive_projects inlinePoll_projects
    multicast_projects transmit_projects d cqes item

theorem batch_projects (items : List Env.BatchItem) :
    ProjectsPrefix rxEvent id (batch items) (RxHistory.batch items) := by
  rw [TrafficSource.batch_factor]
  apply TrafficSource.batch_projects rxEvent _ _ _ _ _ afterBatch_projects items
  intro d cqes item
  have step : (projectStep id : ForInStep (List Int) → ForInStep (List Int)) = id := by
    funext x; cases x <;> rfl
  rw [step]
  exact batchItem_projects d cqes item

theorem inject_appends (family port : Nat) (msg : List UInt8)
    (tos : Nat) (ll : Bool) (dest : Nat) : Appends (inject family port msg tos ll dest) :=
  TrafficSource.inject_appends _ _ _ receive_appends Deferred.crypt_appends drained_appends
    family port msg tos ll dest

theorem afterBatch_appends : Appends afterBatch :=
  TrafficSource.afterBatch_appends _ _ _ _ _ Deferred.crypt_appends Deferred.send_appends
    Deferred.sendOne_appends Scheduler.schedule_appends drained_appends

theorem flood_appends (count port family : Nat) (messages : List (List UInt8)) :
    Appends (flood count port family messages) :=
  TrafficSource.flood_appends _ _ _ _ receive_appends inlinePoll_appends afterBatch_appends
    drained_appends count port family messages

theorem batchItem_appends (d : Device) (cqes : List Int) (item : Env.BatchItem) :
    Appends (batchItem d cqes item) :=
  batchItemWith_appends _ _ _ _ receive_appends inlinePoll_appends multicast_appends
    transmit_appends d cqes item

theorem batch_appends (items : List Env.BatchItem) : Appends (batch items) :=
  TrafficSource.batch_appends _ _ batchItem_appends afterBatch_appends items

theorem inject_preserves (entry : RemoteMap) (family port : Nat) (msg : List UInt8)
    (tos : Nat) (ll : Bool) (dest : Nat) :
    PrefixPreserves (Inv entry) Safe (inject family port msg tos ll dest) :=
  TrafficSource.inject_preserves (safe entry) (store_inv entry) _ _ _
    (receive_preserves entry) (Deferred.crypt_preserves entry) (drained_preserves entry)
    family port msg tos ll dest

theorem afterBatch_preserves (entry : RemoteMap) :
    PrefixPreserves (Inv entry) Safe afterBatch :=
  TrafficSource.afterBatch_preserves (safe entry) (store_inv entry) _ _ _ _ _
    (Deferred.crypt_preserves entry) (Deferred.send_preserves entry)
    (Deferred.sendOne_preserves entry) (Scheduler.schedule_preserves entry) (drained_preserves entry)

theorem flood_preserves (entry : RemoteMap) (count port family : Nat)
    (messages : List (List UInt8)) :
    PrefixPreserves (Inv entry) Safe (flood count port family messages) :=
  TrafficSource.flood_preserves (safe entry) (store_inv entry) _ _ _ _
    (receive_preserves entry) (inlinePoll_preserves entry) (afterBatch_preserves entry)
    (drained_preserves entry) count port family messages

theorem batchItem_preserves (entry : RemoteMap) (d : Device)
    (cqes : List Int) (item : Env.BatchItem) :
    PrefixPreserves (Inv entry) Safe (batchItem d cqes item) :=
  batchItemWith_preserves (safe entry) (wg_store_inv entry) _ _ _ _
    (receive_preserves entry) (inlinePoll_preserves entry)
    (multicast_preserves entry) (transmit_preserves entry) d cqes item

theorem batch_preserves (entry : RemoteMap) (items : List Env.BatchItem) :
    PrefixPreserves (Inv entry) Safe (batch items) :=
  TrafficSource.batch_preserves (safe entry) (store_inv entry) _ _
    (batchItem_preserves entry) (afterBatch_preserves entry) items

end Leanux.Proofs.WG.Roaming.RemoteDriver.Traffic

namespace Leanux.Proofs.WG.Roaming.RemoteDriver.Traffic
open Leanux Leanux.WG Noise Queues Lifetimes Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do

theorem receive_erases (msg : List UInt8) (src : SkbSource) :
    ErasesPrefix (receive msg src) (liftWG (wgReceive msg src)) :=
  projection_erases (receive_projects msg src)
    (RxHistory.mixed_erases (liftWGObserver_erases (wgReceivePrefix_erases msg src)))
theorem transmit_erases (family addr : Nat) (packets : List Packet) (mtu : Nat) :
    ErasesPrefix (transmit family addr packets mtu) (liftWG (wgXmit family addr packets mtu)) :=
  projection_erases (transmit_projects family addr packets mtu)
    (RxHistory.mixed_erases (liftWGObserver_erases (wgXmitPrefix_erases family addr packets mtu)))
theorem multicast_erases (family addr : Nat) :
    ErasesPrefix (multicast family addr) (Env.xmitMulticastLoop family addr) :=
  projection_erases (multicast_projects family addr)
    (RxHistory.audit_erases (xmitMulticastLoopAudit_erases family addr))
theorem drained_erases (what : String) (flags : List Bool) :
    ErasesPrefix (drained what flags) (Env.requireDrained what flags) :=
  projection_erases (drained_projects what flags)
    (RxHistory.mixed_erases (requireDrainedPrefix_erases what flags))
theorem inlinePoll_erases : ErasesPrefix inlinePoll Env.pollScheduledInline :=
  projection_erases inlinePoll_projects RxHistory.pollScheduledInline_erases
theorem inject_erases (family port : Nat) (msg : List UInt8)
    (tos : Nat) (ll : Bool) (dest : Nat) :
    ErasesPrefix (inject family port msg tos ll dest) (Env.inject family port msg tos ll dest) :=
  projection_erases (inject_projects family port msg tos ll dest)
    (RxHistory.inject_erases family port msg tos ll dest)
theorem afterBatch_erases : ErasesPrefix afterBatch Env.afterBatch :=
  projection_erases afterBatch_projects RxHistory.afterBatch_erases
theorem flood_erases (count port family : Nat) (messages : List (List UInt8)) :
    ErasesPrefix (flood count port family messages) (Env.flood count port family messages) :=
  projection_erases (flood_projects count port family messages)
    (RxHistory.flood_erases count port family messages)
theorem batchItem_erases (d : Device) (cqes : List Int) (item : Env.BatchItem) :
    ErasesPrefix (batchItem d cqes item) (Environment.batchItemSource d cqes item) :=
  projection_erases (batchItem_projects d cqes item) (RxHistory.batchItem_erases d cqes item)
theorem batch_erases (items : List Env.BatchItem) : ErasesPrefix (batch items) (Env.batch items) :=
  projection_erases (batch_projects items) (RxHistory.batch_erases items)

end Leanux.Proofs.WG.Roaming.RemoteDriver.Traffic
