import Leanux.Proofs.WG.TimerDiscipline.HookSchedulerCommonSource
import Leanux.Proofs.WG.Progress.TrafficErasureSource

/-! Actual traffic source factories with the common session/hook journal.
Admission and raw transmit queue work; every subsequent scheduler or inline
NAPI callback is observed. These contracts retain reached receipts on Stop. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.TimerDiscipline.HookTraffic
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues
open HandshakeJournal
abbrev Obs := PrefixM Event

def receive (msg : List UInt8) (src : SkbSource) : Obs Unit :=
  liftPrefix (liftWG (wgReceive msg src))
def transmit (family addr : Nat) (packets : List Packet) (mtu : Nat) : Obs Int :=
  liftPrefix (liftWG (wgXmit family addr packets mtu))
def multicast (family addr : Nat) : Obs Unit :=
  liftPrefix (Env.xmitMulticastLoop family addr)
def drained (what : String) (queues : List Bool) : Obs Unit :=
  liftPrefix (Env.requireDrained what queues)

def inject (family port : Nat) (msg : List UInt8) (tos : Nat) (ll : Bool) (dest : Nat) : Obs Int :=
  TrafficSource.injectWith receive (HookCommon.deferred .crypt) drained family port msg tos ll dest
def afterBatch : Obs Unit :=
  TrafficSource.afterBatchWith (HookCommon.deferred .crypt) (HookCommon.deferred .sendAll)
    HookCommon.sendOne (fun worker=>HookCommon.schedule worker) drained
def flood (count port family : Nat) (messages : List (List UInt8)) : Obs Int :=
  TrafficSource.floodWith receive HookCommon.inline afterBatch drained count port family messages
def batchItem (device : Device) (cqes : List Int) (item : Env.BatchItem) :
    Obs (ForInStep (List Int)) :=
  batchItemWith receive HookCommon.inline multicast transmit device cqes item
def batch (items : List Env.BatchItem) : Obs Int :=
  TrafficSource.batchWith batchItem afterBatch items

namespace History

theorem quiet (S : List Event → Prop) {α : Type} (action : Leanux.M α) :
    PrefixPreserves (fun h _=>S h) S (liftPrefix action) :=
  PrefixEnsures.preserves (PrefixEnsures.lift action (fun _ _ hi=>hi)
    (fun _ _ _ _ hi _=>hi))

theorem inject_preserves (S : List Event → Prop)
    (crypt : PrefixPreserves (fun h _=>S h) S (HookCommon.deferred .crypt))
    (family port : Nat) (msg : List UInt8) (tos : Nat) (ll : Bool) (dest : Nat) :
    PrefixPreserves (fun h _=>S h) S (inject family port msg tos ll dest) :=
  TrafficSource.inject_preserves (I:=fun h _=>S h) (S:=S)
    (fun _ _ hi=>hi) (fun _ _ _ _ hi=>hi) _ _ _
    (fun _ _=>quiet S _) crypt (fun _ _=>quiet S _)
    family port msg tos ll dest

theorem afterBatch_preserves (S : List Event → Prop)
    (crypt : PrefixPreserves (fun h _=>S h) S (HookCommon.deferred .crypt))
    (send : PrefixPreserves (fun h _=>S h) S (HookCommon.deferred .sendAll))
    (one : PrefixPreserves (fun h _=>S h) S HookCommon.sendOne)
    (schedule : ∀ worker, PrefixPreserves (fun h _=>S h) S (HookCommon.schedule worker)) :
    PrefixPreserves (fun h _=>S h) S afterBatch :=
  TrafficSource.afterBatch_preserves (I:=fun h _=>S h) (S:=S)
    (fun _ _ hi=>hi) (fun _ _ _ _ hi=>hi) _ _ _ _ _
    crypt send one schedule (fun _ _=>quiet S _)

theorem flood_preserves (S : List Event → Prop)
    (poll : PrefixPreserves (fun h _=>S h) S HookCommon.inline)
    (after : PrefixPreserves (fun h _=>S h) S afterBatch)
    (count port family : Nat) (messages : List (List UInt8)) :
    PrefixPreserves (fun h _=>S h) S (flood count port family messages) :=
  TrafficSource.flood_preserves (I:=fun h _=>S h) (S:=S)
    (fun _ _ hi=>hi) (fun _ _ _ _ hi=>hi) _ _ _ _
    (fun _ _=>quiet S _) poll after (fun _ _=>quiet S _) count port family messages

theorem batchItem_preserves (S : List Event → Prop)
    (poll : PrefixPreserves (fun h _=>S h) S HookCommon.inline)
    (device : Device) (cqes : List Int) (item : Env.BatchItem) :
    PrefixPreserves (fun h _=>S h) S (batchItem device cqes item) :=
  batchItemWith_preserves (I:=fun h _=>S h) (S:=S)
    (fun _ _ hi=>hi) (fun _ _ _ _ hi=>hi) _ _ _ _
    (fun _ _=>quiet S _) poll (fun _ _=>quiet S _)
    (fun _ _ _ _=>quiet S _) device cqes item

theorem batch_preserves (S : List Event → Prop)
    (one : ∀ device cqes item, PrefixPreserves (fun h _=>S h) S (batchItem device cqes item))
    (after : PrefixPreserves (fun h _=>S h) S afterBatch)
    (items : List Env.BatchItem) :
    PrefixPreserves (fun h _=>S h) S (batch items) :=
  TrafficSource.batch_preserves (I:=fun h _=>S h) (S:=S)
    (fun _ _ hi=>hi) (fun _ _ _ _ hi=>hi) _ _ one after items

end History

theorem inject_valid (family port : Nat) (msg : List UInt8) (tos : Nat) (ll : Bool) (dest : Nat) :
    PrefixPreserves (fun h _=>ValidHistory h) ValidHistory (inject family port msg tos ll dest) :=
  History.inject_preserves ValidHistory (HookCommon.deferred_valid .crypt) family port msg tos ll dest
theorem inject_paired (family port : Nat) (msg : List UInt8) (tos : Nat) (ll : Bool) (dest : Nat) :
    PrefixPreserves (fun h _=>Paired h) Paired (inject family port msg tos ll dest) :=
  History.inject_preserves Paired (HookCommon.deferred_paired .crypt) family port msg tos ll dest

theorem afterBatch_valid : PrefixPreserves (fun h _=>ValidHistory h) ValidHistory afterBatch :=
  History.afterBatch_preserves ValidHistory (HookCommon.deferred_valid .crypt)
    (HookCommon.deferred_valid .sendAll) HookCommon.sendOne_valid HookCommon.schedule_valid
theorem afterBatch_paired : PrefixPreserves (fun h _=>Paired h) Paired afterBatch :=
  History.afterBatch_preserves Paired (HookCommon.deferred_paired .crypt)
    (HookCommon.deferred_paired .sendAll) HookCommon.sendOne_paired HookCommon.schedule_paired

theorem flood_valid (count port family : Nat) (messages : List (List UInt8)) :
    PrefixPreserves (fun h _=>ValidHistory h) ValidHistory (flood count port family messages) :=
  History.flood_preserves ValidHistory HookCommon.inline_valid afterBatch_valid count port family messages
theorem flood_paired (count port family : Nat) (messages : List (List UInt8)) :
    PrefixPreserves (fun h _=>Paired h) Paired (flood count port family messages) :=
  History.flood_preserves Paired HookCommon.inline_paired afterBatch_paired count port family messages

theorem batchItem_valid (device : Device) (cqes : List Int) (item : Env.BatchItem) :
    PrefixPreserves (fun h _=>ValidHistory h) ValidHistory (batchItem device cqes item) :=
  History.batchItem_preserves ValidHistory HookCommon.inline_valid device cqes item
theorem batchItem_paired (device : Device) (cqes : List Int) (item : Env.BatchItem) :
    PrefixPreserves (fun h _=>Paired h) Paired (batchItem device cqes item) :=
  History.batchItem_preserves Paired HookCommon.inline_paired device cqes item

theorem batch_valid (items : List Env.BatchItem) :
    PrefixPreserves (fun h _=>ValidHistory h) ValidHistory (batch items) :=
  History.batch_preserves ValidHistory batchItem_valid afterBatch_valid items
theorem batch_paired (items : List Env.BatchItem) :
    PrefixPreserves (fun h _=>Paired h) Paired (batch items) :=
  History.batch_preserves Paired batchItem_paired afterBatch_paired items

theorem inject_erases (family port : Nat) (msg : List UInt8) (tos : Nat) (ll : Bool) (dest : Nat) :
    ErasesPrefix (inject family port msg tos ll dest) (Env.inject family port msg tos ll dest) :=
  Progress.TrafficErasure.inject _ _ _ (fun _ _=>erasesPrefix_lift _)
    (HookCommon.deferred_erases .crypt) (fun _ _=>erasesPrefix_lift _) family port msg tos ll dest
theorem afterBatch_erases : ErasesPrefix afterBatch Env.afterBatch :=
  Progress.TrafficErasure.afterBatch _ _ _ _ _ (HookCommon.deferred_erases .crypt)
    (HookCommon.deferred_erases .sendAll) HookCommon.sendOne_erases HookCommon.schedule_erases
    (fun _ _=>erasesPrefix_lift _)
theorem flood_erases (count port family : Nat) (messages : List (List UInt8)) :
    ErasesPrefix (flood count port family messages) (Env.flood count port family messages) :=
  Progress.TrafficErasure.flood _ _ _ _ (fun _ _=>erasesPrefix_lift _)
    HookCommon.inline_erases afterBatch_erases (fun _ _=>erasesPrefix_lift _) count port family messages
theorem batchItem_erases (device : Device) (cqes : List Int) (item : Env.BatchItem) :
    ErasesPrefix (batchItem device cqes item) (Environment.batchItemSource device cqes item) :=
  Progress.TrafficErasure.batchItem _ _ _ _ (fun _ _=>erasesPrefix_lift _) HookCommon.inline_erases
    (fun _ _=>erasesPrefix_lift _) (fun _ _ _ _=>erasesPrefix_lift _) device cqes item
theorem batch_erases (items : List Env.BatchItem) :
    ErasesPrefix (batch items) (Env.batch items) :=
  Progress.TrafficErasure.batch _ _ batchItem_erases afterBatch_erases items

theorem inject_appends (family port : Nat) (msg : List UInt8) (tos : Nat) (ll : Bool) (dest : Nat) :
    Appends (inject family port msg tos ll dest) :=
  TrafficSource.inject_appends _ _ _ (fun _ _=>Appends.lift _) (HookCommon.deferred_appends .crypt)
    (fun _ _=>Appends.lift _) family port msg tos ll dest
theorem afterBatch_appends : Appends afterBatch :=
  TrafficSource.afterBatch_appends _ _ _ _ _ (HookCommon.deferred_appends .crypt)
    (HookCommon.deferred_appends .sendAll) HookCommon.sendOne_appends HookCommon.schedule_appends
    (fun _ _=>Appends.lift _)
theorem flood_appends (count port family : Nat) (messages : List (List UInt8)) :
    Appends (flood count port family messages) :=
  TrafficSource.flood_appends _ _ _ _ (fun _ _=>Appends.lift _) HookCommon.inline_appends
    afterBatch_appends (fun _ _=>Appends.lift _) count port family messages
theorem batchItem_appends (device : Device) (cqes : List Int) (item : Env.BatchItem) :
    Appends (batchItem device cqes item) :=
  batchItemWith_appends _ _ _ _ (fun _ _=>Appends.lift _) HookCommon.inline_appends
    (fun _ _=>Appends.lift _) (fun _ _ _ _=>Appends.lift _) device cqes item
theorem batch_appends (items : List Env.BatchItem) : Appends (batch items) :=
  TrafficSource.batch_appends _ _ batchItem_appends afterBatch_appends items

end Leanux.Proofs.WG.TimerDiscipline.HookTraffic
