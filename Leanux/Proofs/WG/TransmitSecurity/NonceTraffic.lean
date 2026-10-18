import Leanux.Proofs.WG.TransmitSecurity.NonceEntryFrames
import Leanux.Proofs.WG.Lifetimes.TrafficPreservation
import Leanux.Proofs.WG.Lifetimes.TxCallSource

/-! Native fixture traffic retains the nonce journal through receive, transmit,
inline polling and deferred workers. Source guards and stopped prefixes remain
those of the executable environment. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Nonce
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues

def receiveEntryObserved (msg : List UInt8) (src : SkbSource) : PrefixM Allocation Unit :=
  liftPrefix (liftWG (wgReceive msg src))

def multicastObserved (family addr : Nat) : PrefixM Allocation Unit :=
  liftPrefix (Env.xmitMulticastLoop family addr)

def drainObserved (what : String) (flags : List Bool) : PrefixM Allocation Unit :=
  liftPrefix (Env.requireDrained what flags)

def injectObserved (family port : Nat) (msg : List UInt8) (tos : Nat) (ll : Bool) (dest : Nat) : PrefixM Allocation Int :=
  TrafficSource.injectWith receiveEntryObserved cryptObserved drainObserved family port msg tos ll dest

def afterBatchObserved : PrefixM Allocation Unit :=
  TrafficSource.afterBatchWith cryptObserved sendWorkersObserved
    (liftPrefix Env.runOneSendWorker) (fun stack => scheduleObserved stack) drainObserved

def floodObserved (count port family : Nat) (messages : List (List UInt8)) : PrefixM Allocation Int :=
  TrafficSource.floodWith receiveEntryObserved inlinePollObserved afterBatchObserved drainObserved count port family messages

def batchItemObserved (d : Device) (cqes : List Int) (item : Env.BatchItem) : PrefixM Allocation (ForInStep (List Int)) :=
  batchItemWith receiveEntryObserved inlinePollObserved multicastObserved
    (fun family addr packets mtu => liftWGObserver (transmitObserved family addr packets mtu)) d cqes item

def batchObserved (items : List Env.BatchItem) : PrefixM Allocation Int :=
  TrafficSource.batchWith batchItemObserved afterBatchObserved items

def syscallXmitObserved (family addr : Nat) (payload : List UInt8) (opts : Env.XmitOpts) : PrefixM Allocation Int :=
  syscallXmitWith multicastObserved
    (fun family addr packets mtu => liftWGObserver (transmitObserved family addr packets mtu)) family addr payload opts

theorem receiveEntryObserved_safe (msg : List UInt8) (src : SkbSource) :
    PrefixPreserves (fun h w => Inv (view w.wg) h) List.Nodup (receiveEntryObserved msg src) :=
  Frames.product_native (Frames.rx_entry msg src)

theorem multicastObserved_safe (family addr : Nat) :
    PrefixPreserves (fun h w => Inv (view w.wg) h) List.Nodup (multicastObserved family addr) :=
  Frames.product_lift (Frames.multicast family addr)

theorem drainObserved_safe (what : String) (flags : List Bool) :
    PrefixPreserves (fun h w => Inv (view w.wg) h) List.Nodup (drainObserved what flags) :=
  Frames.stored (Frames.drained what flags)

theorem injectObserved_safe (family port : Nat) (msg : List UInt8) (tos : Nat) (ll : Bool) (dest : Nat) :
    PrefixPreserves (fun h w => Inv (view w.wg) h) List.Nodup (injectObserved family port msg tos ll dest) :=
  TrafficSource.inject_preserves (fun _ _ hi => hi.nodup) Frames.product_store
    _ _ _ receiveEntryObserved_safe cryptObserved_safe drainObserved_safe family port msg tos ll dest

theorem afterBatchObserved_safe :
    PrefixPreserves (fun h w => Inv (view w.wg) h) List.Nodup afterBatchObserved :=
  TrafficSource.afterBatch_preserves (fun _ _ hi => hi.nodup) Frames.product_store
    _ _ _ _ _ cryptObserved_safe sendWorkersObserved_safe (Frames.product_lift Frames.one_send)
    scheduleObserved_safe drainObserved_safe

theorem floodObserved_safe (count port family : Nat) (messages : List (List UInt8)) :
    PrefixPreserves (fun h w => Inv (view w.wg) h) List.Nodup (floodObserved count port family messages) :=
  TrafficSource.flood_preserves (fun _ _ hi => hi.nodup) Frames.product_store
    _ _ _ _ receiveEntryObserved_safe inlinePollObserved_safe afterBatchObserved_safe drainObserved_safe
    count port family messages

theorem batchItemObserved_safe (d : Device) (cqes : List Int) (item : Env.BatchItem) :
    PrefixPreserves (fun h w => Inv (view w.wg) h) List.Nodup (batchItemObserved d cqes item) :=
  batchItemWith_preserves (fun _ _ hi => hi.nodup) Frames.wg_store _ _ _ _
    receiveEntryObserved_safe inlinePollObserved_safe multicastObserved_safe
    (fun family addr packets mtu => (transmitObserved_safe family addr packets mtu).liftWGObserver) d cqes item

theorem batchObserved_safe (items : List Env.BatchItem) :
    PrefixPreserves (fun h w => Inv (view w.wg) h) List.Nodup (batchObserved items) :=
  TrafficSource.batch_preserves (fun _ _ hi => hi.nodup) Frames.product_store _ _
    batchItemObserved_safe afterBatchObserved_safe items

theorem syscallXmitObserved_safe (family addr : Nat) (payload : List UInt8) (opts : Env.XmitOpts) :
    PrefixPreserves (fun h w => Inv (view w.wg) h) List.Nodup (syscallXmitObserved family addr payload opts) :=
  syscallXmitWith_preserves (fun _ _ hi => hi.nodup) Frames.wg_store _ _ multicastObserved_safe
    (fun family addr packets mtu => (transmitObserved_safe family addr packets mtu).liftWGObserver) family addr payload opts

macro "nonce_traffic_erasure" : tactic => `(tactic| first
  | (maintenance_head receiveEntryObserved; exact erasesPrefix_lift _)
  | (maintenance_head multicastObserved; exact erasesPrefix_lift _)
  | (maintenance_head drainObserved; exact erasesPrefix_lift _)
  | (maintenance_head transmitObserved; exact liftWGObserver_erases (transmitObserved_erases _ _ _ _))
  | (maintenance_head cryptObserved; exact cryptObserved_erases)
  | (maintenance_head sendWorkersObserved; exact sendWorkersObserved_erases)
  | (maintenance_head scheduleObserved; exact scheduleObserved_erases _)
  | (maintenance_head inlinePollObserved; exact inlinePollObserved_erases)
  | (maintenance_head runWorkerPrefix; apply runWorkerPrefix_erases)
  | (maintenance_head ForIn.forIn; apply erasesPrefix_forIn)
  | nonce_deferred_erasure)

theorem injectObserved_erases (family port : Nat) (msg : List UInt8) (tos : Nat) (ll : Bool) (dest : Nat) :
    ErasesPrefix (injectObserved family port msg tos ll dest) (Env.inject family port msg tos ll dest) := by
  unfold injectObserved TrafficSource.injectWith Env.inject
  repeat' nonce_traffic_erasure

theorem afterBatchObserved_erases : ErasesPrefix afterBatchObserved Env.afterBatch := by
  unfold afterBatchObserved TrafficSource.afterBatchWith Env.afterBatch
  repeat' nonce_traffic_erasure

theorem floodObserved_erases (count port family : Nat) (messages : List (List UInt8)) :
    ErasesPrefix (floodObserved count port family messages) (Env.flood count port family messages) := by
  unfold floodObserved TrafficSource.floodWith Env.flood
  repeat' first
    | (maintenance_head afterBatchObserved; exact afterBatchObserved_erases)
    | nonce_traffic_erasure

theorem batchItemObserved_erases (d : Device) (cqes : List Int) (item : Env.BatchItem) :
    ErasesPrefix (batchItemObserved d cqes item) (Environment.batchItemSource d cqes item) := by
  cases item <;> unfold batchItemObserved batchItemWith Environment.batchItemSource
  all_goals repeat' nonce_traffic_erasure

theorem batchObserved_erases (items : List Env.BatchItem) :
    ErasesPrefix (batchObserved items) (Env.batch items) := by
  rw [← Environment.batchSource_eq]
  unfold batchObserved TrafficSource.batchWith Environment.batchSource
  repeat' first
    | (maintenance_head afterBatchObserved; exact afterBatchObserved_erases)
    | (maintenance_head batchItemObserved; exact batchItemObserved_erases _ _ _)
    | (maintenance_head ForIn.forIn; apply erasesPrefix_forIn)
    | nonce_traffic_erasure

theorem syscallXmitObserved_erases (family addr : Nat) (payload : List UInt8) (opts : Env.XmitOpts) :
    ErasesPrefix (syscallXmitObserved family addr payload opts) (Leanux.dispatch (.wgXmit family addr payload opts)) := by
  unfold syscallXmitObserved syscallXmitWith Leanux.dispatch
  apply Configuration.socketCallOnWith_erases
  repeat' nonce_traffic_erasure

end Leanux.Proofs.WG.TransmitSecurity.Nonce
