import Leanux.Proofs.WG.TimerDiscipline.HookTrafficFrontierFrames
import Leanux.Proofs.WG.TimerDiscipline.SessionFrontierBridge
import Leanux.Proofs.WG.TimerDiscipline.HookTrafficSource

/-! Frontier transport through the unchanged common traffic observers.
Every premise names an actual queued-work or inline callback. Normal exits
retain the current counter bound; all outcomes retain ordered history.
These are composition rules, not an initialized uniqueness conclusion. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.TimerDiscipline.HookTraffic
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues HandshakeJournal

theorem receive_frontier (msg : List UInt8) (src : SkbSource) :
    PrefixPreserves (fun h w=>Frontier h w.wg.keypairCounter) Ordered (receive msg src) :=
  quiet_frontier _ (FrontierFrames.receive_counter msg src)

theorem transmit_frontier (family addr : Nat) (packets : List Packet) (mtu : Nat) :
    PrefixPreserves (fun h w=>Frontier h w.wg.keypairCounter) Ordered (transmit family addr packets mtu) :=
  quiet_frontier _ (FrontierFrames.transmit_counter family addr packets mtu)

theorem multicast_frontier (family addr : Nat) :
    PrefixPreserves (fun h w=>Frontier h w.wg.keypairCounter) Ordered (multicast family addr) :=
  quiet_frontier _ (FrontierFrames.multicast_counter family addr)

theorem drained_frontier (what : String) (queues : List Bool) :
    PrefixPreserves (fun h w=>Frontier h w.wg.keypairCounter) Ordered (drained what queues) :=
  quiet_frontier _ (FrontierFrames.drained_counter what queues)

theorem inject_frontier
    (crypt : PrefixPreserves (fun h w=>Frontier h w.wg.keypairCounter) Ordered
      (HookCommon.deferred .crypt))
    (family port : Nat) (msg : List UInt8) (tos : Nat) (ll : Bool) (dest : Nat) :
    PrefixPreserves (fun h w=>Frontier h w.wg.keypairCounter) Ordered
      (inject family port msg tos ll dest) :=
  TrafficSource.inject_preserves
    (I:=fun h w=>Frontier h w.wg.keypairCounter) (S:=Ordered)
    (fun _ _ hi=>hi.1) frontier_store _ _ _
    receive_frontier crypt drained_frontier family port msg tos ll dest

theorem afterBatch_frontier
    (crypt : PrefixPreserves (fun h w=>Frontier h w.wg.keypairCounter) Ordered
      (HookCommon.deferred .crypt))
    (send : PrefixPreserves (fun h w=>Frontier h w.wg.keypairCounter) Ordered
      (HookCommon.deferred .sendAll))
    (one : PrefixPreserves (fun h w=>Frontier h w.wg.keypairCounter) Ordered HookCommon.sendOne)
    (schedule : ∀ worker, PrefixPreserves (fun h w=>Frontier h w.wg.keypairCounter) Ordered
      (HookCommon.schedule worker)) :
    PrefixPreserves (fun h w=>Frontier h w.wg.keypairCounter) Ordered afterBatch :=
  TrafficSource.afterBatch_preserves
    (I:=fun h w=>Frontier h w.wg.keypairCounter) (S:=Ordered)
    (fun _ _ hi=>hi.1) frontier_store _ _ _ _ _
    crypt send one schedule drained_frontier

theorem flood_frontier
    (poll : PrefixPreserves (fun h w=>Frontier h w.wg.keypairCounter) Ordered HookCommon.inline)
    (after : PrefixPreserves (fun h w=>Frontier h w.wg.keypairCounter) Ordered afterBatch)
    (count port family : Nat) (messages : List (List UInt8)) :
    PrefixPreserves (fun h w=>Frontier h w.wg.keypairCounter) Ordered
      (flood count port family messages) :=
  TrafficSource.flood_preserves
    (I:=fun h w=>Frontier h w.wg.keypairCounter) (S:=Ordered)
    (fun _ _ hi=>hi.1) frontier_store _ _ _ _
    receive_frontier poll after drained_frontier count port family messages

theorem batchItem_frontier
    (poll : PrefixPreserves (fun h w=>Frontier h w.wg.keypairCounter) Ordered HookCommon.inline)
    (device : Device) (cqes : List Int) (item : Env.BatchItem) :
    PrefixPreserves (fun h w=>Frontier h w.wg.keypairCounter) Ordered
      (batchItem device cqes item) :=
  batchItemWith_preserves
    (I:=fun h w=>Frontier h w.wg.keypairCounter) (S:=Ordered)
    (fun _ _ hi=>hi.1) (fun h w v=>frontier_wg_store h w.wg v.wg)
    _ _ _ _ receive_frontier poll multicast_frontier transmit_frontier device cqes item

theorem batch_frontier
    (one : ∀ device cqes item,
      PrefixPreserves (fun h w=>Frontier h w.wg.keypairCounter) Ordered (batchItem device cqes item))
    (after : PrefixPreserves (fun h w=>Frontier h w.wg.keypairCounter) Ordered afterBatch)
    (items : List Env.BatchItem) :
    PrefixPreserves (fun h w=>Frontier h w.wg.keypairCounter) Ordered (batch items) :=
  TrafficSource.batch_preserves
    (I:=fun h w=>Frontier h w.wg.keypairCounter) (S:=Ordered)
    (fun _ _ hi=>hi.1) frontier_store _ _ one after items

end Leanux.Proofs.WG.TimerDiscipline.HookTraffic
