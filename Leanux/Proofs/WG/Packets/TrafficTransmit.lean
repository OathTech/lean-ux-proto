import Leanux.Proofs.WG.Lifetimes.TrafficPreservation
import Leanux.Proofs.WG.Packets.TransmitRx
import Leanux.Proofs.WG.AllowedIps.RoutingEnvWorkersFrames

/-! Concrete traffic callers retain their original fixture, route and CQE
handling. Polling and deferred workers are explicit callbacks; direct batch
transmits execute the native handoff observer. -/
namespace Leanux.Proofs.WG.TransmitJoint.Traffic
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes Queues AllowedIps

def receive (msg : List UInt8) (src : SkbSource) : PrefixM Event Unit :=
  oldRx (RxHistory.mixed (liftWGObserver (wgReceivePrefix msg src)))
def drained (what : String) (flags : List Bool) : PrefixM Event Unit :=
  oldRx (RxHistory.mixed (requireDrainedPrefix what flags))
def sendOne : PrefixM Event Unit := oldRx (RxHistory.audit runOneSendWorkerAudit)

def item (poll : PrefixM Event Unit) (d : Device) (cqes : List Int) (i : Env.BatchItem) :
    PrefixM Event (ForInStep (List Int)) :=
  batchItemWith receive poll multicast (fun f a p m => liftWGObserver (transmit f a p m)) d cqes i

def inject (crypt : PrefixM Event Unit)
    (family port : Nat) (msg : List UInt8) (tos : Nat) (ll : Bool) (dest : Nat) : PrefixM Event Int :=
  TrafficSource.injectWith receive crypt drained family port msg tos ll dest

def afterBatch (crypt send : PrefixM Event Unit) (schedule : Option Worker → PrefixM Event Unit) :
    PrefixM Event Unit := TrafficSource.afterBatchWith crypt send sendOne schedule drained

def flood (poll after : PrefixM Event Unit) (count port family : Nat) (messages : List (List UInt8)) :
    PrefixM Event Int := TrafficSource.floodWith receive poll after drained count port family messages

def batch (poll after : PrefixM Event Unit) (items : List Env.BatchItem) : PrefixM Event Int :=
  TrafficSource.batchWith (item poll) after items

theorem receive_preserves (initial : FlatTable × FlatTable) (msg : List UInt8) (src : SkbSource) :
    PrefixPreserves (Inv initial) (Safe initial) (receive msg src) :=
  oldRx_preserves initial _ _ (RxHistory.mixed_erases (liftWGObserver_erases (wgReceivePrefix_erases msg src)))
    (wgReceive_routing msg src).liftWG

theorem drained_preserves (initial : FlatTable × FlatTable) (what : String) (flags : List Bool) :
    PrefixPreserves (Inv initial) (Safe initial) (drained what flags) :=
  oldRx_preserves initial _ _ (RxHistory.mixed_erases (requireDrainedPrefix_erases what flags))
    (ProjectedRetainsRoutingCall.of_same (requireDrained_routing what flags))

theorem sendOne_preserves (initial : FlatTable × FlatTable) :
    PrefixPreserves (Inv initial) (Safe initial) sendOne :=
  oldRx_preserves initial _ _ (RxHistory.audit_erases runOneSendWorkerAudit_erases) runOneSendWorker_routing

theorem item_preserves (initial : FlatTable × FlatTable) (poll : PrefixM Event Unit)
    (hp : PrefixPreserves (Inv initial) (Safe initial) poll) (d : Device) (cqes : List Int) (i : Env.BatchItem) :
    PrefixPreserves (Inv initial) (Safe initial) (item poll d cqes i) :=
  batchItemWith_preserves (fun _ _ hi => hi.safe) Inv.store receive poll multicast _
    (receive_preserves initial) hp (multicast_preserves initial) (transmit_product initial) d cqes i

theorem inject_preserves (initial : FlatTable × FlatTable) (crypt : PrefixM Event Unit)
    (hc : PrefixPreserves (Inv initial) (Safe initial) crypt)
    (family port : Nat) (msg : List UInt8) (tos : Nat) (ll : Bool) (dest : Nat) :
    PrefixPreserves (Inv initial) (Safe initial) (inject crypt family port msg tos ll dest) :=
  TrafficSource.inject_preserves (fun _ _ hi => hi.safe) Inv.productStore receive crypt drained
    (receive_preserves initial) hc (drained_preserves initial) family port msg tos ll dest

theorem afterBatch_preserves (initial : FlatTable × FlatTable) (crypt send : PrefixM Event Unit)
    (schedule : Option Worker → PrefixM Event Unit)
    (hc : PrefixPreserves (Inv initial) (Safe initial) crypt)
    (hs : PrefixPreserves (Inv initial) (Safe initial) send)
    (hsch : ∀ stack, PrefixPreserves (Inv initial) (Safe initial) (schedule stack)) :
    PrefixPreserves (Inv initial) (Safe initial) (afterBatch crypt send schedule) :=
  TrafficSource.afterBatch_preserves (fun _ _ hi => hi.safe) Inv.productStore crypt send sendOne schedule drained
    hc hs (sendOne_preserves initial) hsch (drained_preserves initial)

theorem flood_preserves (initial : FlatTable × FlatTable) (poll after : PrefixM Event Unit)
    (hp : PrefixPreserves (Inv initial) (Safe initial) poll)
    (ha : PrefixPreserves (Inv initial) (Safe initial) after)
    (count port family : Nat) (messages : List (List UInt8)) :
    PrefixPreserves (Inv initial) (Safe initial) (flood poll after count port family messages) :=
  TrafficSource.flood_preserves (fun _ _ hi => hi.safe) Inv.productStore receive poll after drained
    (receive_preserves initial) hp ha (drained_preserves initial) count port family messages

theorem batch_preserves (initial : FlatTable × FlatTable) (poll after : PrefixM Event Unit)
    (hp : PrefixPreserves (Inv initial) (Safe initial) poll)
    (ha : PrefixPreserves (Inv initial) (Safe initial) after) (items : List Env.BatchItem) :
    PrefixPreserves (Inv initial) (Safe initial) (batch poll after items) :=
  TrafficSource.batch_preserves (fun _ _ hi => hi.safe) Inv.productStore (item poll) after
    (item_preserves initial poll hp) ha items

theorem receive_projects (msg : List UInt8) (src : SkbSource) :
    ProjectsPrefix RxTransmit.globalRx id (receive msg src)
      (RxHistory.mixed (liftWGObserver (wgReceivePrefix msg src))) := oldRx_projects _ (Appends.focus _ _ _)

theorem drained_projects (what : String) (flags : List Bool) :
    ProjectsPrefix RxTransmit.globalRx id (drained what flags)
      (RxHistory.mixed (requireDrainedPrefix what flags)) := oldRx_projects _ (Appends.focus _ _ _)

theorem sendOne_projects : ProjectsPrefix RxTransmit.globalRx id sendOne
    (RxHistory.audit runOneSendWorkerAudit) := oldRx_projects _ (Appends.focus _ _ _)

theorem item_projects (poll : PrefixM Event Unit)
    (hp : ProjectsPrefix RxTransmit.globalRx id poll RxHistory.pollScheduledInline)
    (d : Device) (cqes : List Int) (i : Env.BatchItem) :
    ProjectsPrefix RxTransmit.globalRx id (item poll d cqes i) (RxHistory.batchItem d cqes i) :=
  batchItemWith_projects RxTransmit.globalRx _ _ _ _ _ _ _ _ receive_projects hp multicast_rx transmit_rx d cqes i

theorem inject_projects (crypt : PrefixM Event Unit)
    (hc : ProjectsPrefix RxTransmit.globalRx id crypt RxHistory.runCryptWorkers)
    (family port : Nat) (msg : List UInt8) (tos : Nat) (ll : Bool) (dest : Nat) :
    ProjectsPrefix RxTransmit.globalRx id (inject crypt family port msg tos ll dest)
      (RxHistory.inject family port msg tos ll dest) :=
  TrafficSource.inject_projects RxTransmit.globalRx _ _ _ _ _ _ receive_projects hc drained_projects
    family port msg tos ll dest

theorem afterBatch_projects (crypt send : PrefixM Event Unit) (schedule : Option Worker → PrefixM Event Unit)
    (hc : ProjectsPrefix RxTransmit.globalRx id crypt RxHistory.runCryptWorkers)
    (hs : ProjectsPrefix RxTransmit.globalRx id send RxHistory.runSendWorkers)
    (hsch : ∀ stack, ProjectsPrefix RxTransmit.globalRx id (schedule stack) (RxHistory.schedule stack)) :
    ProjectsPrefix RxTransmit.globalRx id (afterBatch crypt send schedule) RxHistory.afterBatch :=
  TrafficSource.afterBatch_projects RxTransmit.globalRx crypt send sendOne
    RxHistory.runCryptWorkers RxHistory.runSendWorkers (RxHistory.audit runOneSendWorkerAudit)
    schedule (fun stack => RxHistory.schedule stack) drained (fun what flags => RxHistory.mixed (requireDrainedPrefix what flags))
    hc hs sendOne_projects hsch drained_projects

theorem flood_projects (poll after : PrefixM Event Unit)
    (hp : ProjectsPrefix RxTransmit.globalRx id poll RxHistory.pollScheduledInline)
    (ha : ProjectsPrefix RxTransmit.globalRx id after RxHistory.afterBatch)
    (count port family : Nat) (messages : List (List UInt8)) :
    ProjectsPrefix RxTransmit.globalRx id (flood poll after count port family messages)
      (RxHistory.flood count port family messages) :=
  TrafficSource.flood_projects RxTransmit.globalRx _ _ _ _ _ _ _ _ receive_projects hp ha drained_projects
    count port family messages

theorem batch_projects (poll after : PrefixM Event Unit)
    (hp : ProjectsPrefix RxTransmit.globalRx id poll RxHistory.pollScheduledInline)
    (ha : ProjectsPrefix RxTransmit.globalRx id after RxHistory.afterBatch) (items : List Env.BatchItem) :
    ProjectsPrefix RxTransmit.globalRx id (batch poll after items) (RxHistory.batch items) := by
  have step : projectStep (id : List Int → List Int) = id := by
    funext s
    cases s <;> rfl
  apply TrafficSource.batch_projects RxTransmit.globalRx (item poll) RxHistory.batchItem after RxHistory.afterBatch
  · intro d cqes i
    simpa only [step] using item_projects poll hp d cqes i
  · exact ha

theorem item_appends (poll : PrefixM Event Unit) (hp : Appends poll)
    (d : Device) (cqes : List Int) (i : Env.BatchItem) : Appends (item poll d cqes i) :=
  batchItemWith_appends receive poll multicast _ (fun _ _ => oldRx_appends _) hp
    (fun _ _ => oldRx_appends _) (fun f a p m => (transmit_appends f a p m).liftWGObserver) d cqes i

theorem inject_appends (crypt : PrefixM Event Unit) (hc : Appends crypt)
    (family port : Nat) (msg : List UInt8) (tos : Nat) (ll : Bool) (dest : Nat) :
    Appends (inject crypt family port msg tos ll dest) :=
  TrafficSource.inject_appends receive crypt drained (fun _ _ => oldRx_appends _) hc
    (fun _ _ => oldRx_appends _) family port msg tos ll dest

theorem afterBatch_appends (crypt send : PrefixM Event Unit) (schedule : Option Worker → PrefixM Event Unit)
    (hc : Appends crypt) (hs : Appends send) (hsch : ∀ stack, Appends (schedule stack)) :
    Appends (afterBatch crypt send schedule) :=
  TrafficSource.afterBatch_appends crypt send sendOne schedule drained hc hs (oldRx_appends _) hsch
    (fun _ _ => oldRx_appends _)

theorem flood_appends (poll after : PrefixM Event Unit) (hp : Appends poll) (ha : Appends after)
    (count port family : Nat) (messages : List (List UInt8)) :
    Appends (flood poll after count port family messages) :=
  TrafficSource.flood_appends receive poll after drained (fun _ _ => oldRx_appends _) hp ha
    (fun _ _ => oldRx_appends _) count port family messages

theorem batch_appends (poll after : PrefixM Event Unit) (hp : Appends poll) (ha : Appends after)
    (items : List Env.BatchItem) : Appends (batch poll after items) :=
  TrafficSource.batch_appends (item poll) after (item_appends poll hp) ha items

end Leanux.Proofs.WG.TransmitJoint.Traffic
