import Leanux.Proofs.WG.Queues.BaseCoherenceDeferred
import Leanux.Proofs.WG.Queues.BatchAccount

/-! The original traffic callers retain the structural base list and public-key
rows across their actual receives, polls and deferred work. Source executions
keep every recorded guard and error arm. -/
namespace Leanux.Proofs.WG.Queues.RxCredits.BaseCoherence
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do

theorem receive_structure (initial) (msg : List UInt8) (src : SkbSource) :
    PrefixPreserves (fun _ w=>view w.wg=initial) (fun _=>True)
      (RxHistory.mixed (liftWGObserver (wgReceivePrefix msg src))) :=
  observed_structure initial _ _ (Appends.focus _ _ _)
    (RxHistory.mixed_erases (liftWGObserver_erases (wgReceivePrefix_erases msg src)))
    (native_product_view _ (wgReceive_view msg src))

theorem inject_structure (initial) (family port : Nat) (msg : List UInt8)
    (tos : Nat) (ll : Bool) (dest : Nat) :
    PrefixPreserves (fun _ w=>view w.wg=initial) (fun _=>True)
      (RxHistory.inject family port msg tos ll dest) := by
  rw [TrafficSource.inject_factor]
  exact TrafficSource.inject_preserves (fun _ _ _=>True.intro)
    (fun _ _ _ same hi=>(product_view_transport same).trans hi) _ _ _
    (receive_structure initial) (runCryptWorkers_structure initial) (deferred_atoms initial).drained
    family port msg tos ll dest

theorem afterBatch_structure (initial) :
    PrefixPreserves (fun _ w=>view w.wg=initial) (fun _=>True) RxHistory.afterBatch := by
  rw [TrafficSource.afterBatch_factor]
  exact TrafficSource.afterBatch_preserves (fun _ _ _=>True.intro)
    (fun _ _ _ same hi=>(product_view_transport same).trans hi) _ _ _ _ _
    (runCryptWorkers_structure initial) (runSendWorkers_structure initial)
    (deferred_atoms initial).sendOne (schedule_structure initial) (deferred_atoms initial).drained

theorem flood_structure (initial) (count port family : Nat) (messages : List (List UInt8)) :
    PrefixPreserves (fun _ w=>view w.wg=initial) (fun _=>True)
      (RxHistory.flood count port family messages) := by
  rw [TrafficSource.flood_factor]
  exact TrafficSource.flood_preserves (fun _ _ _=>True.intro)
    (fun _ _ _ same hi=>(product_view_transport same).trans hi) _ _ _ _
    (receive_structure initial) (inline_structure initial) (afterBatch_structure initial)
    (deferred_atoms initial).drained count port family messages

theorem multicast_structure (initial) (family addr : Nat) :
    PrefixPreserves (fun _ w=>view w.wg=initial) (fun _=>True)
      (RxHistory.audit (xmitMulticastLoopAudit family addr)) :=
  observed_structure initial _ _ (Appends.focus _ _ _) (RxHistory.audit_erases (xmitMulticastLoopAudit_erases family addr))
    (product_store_view ((pinned_const _private.Leanux.Proofs.WG.Queues.BatchAccount.«0».Leanux.Proofs.WG.Queues.RxCredits.BatchAccount.multicast_store) family addr))

theorem xmit_structure (initial) (family addr : Nat) (packets : List WG.Packet) (mtu : Nat) :
    PrefixPreserves (fun _ w=>view w.wg=initial) (fun _=>True)
      (RxHistory.mixed (liftWGObserver (wgXmitPrefix family addr packets mtu))) :=
  observed_structure initial _ _ (Appends.focus _ _ _)
    (RxHistory.mixed_erases (liftWGObserver_erases (wgXmitPrefix_erases family addr packets mtu)))
    (native_product_view _ (wgXmit_view family addr packets mtu))

theorem batchItem_structure (initial) (d : Device) (cqes : List Int) (item : Env.BatchItem) :
    PrefixPreserves (fun _ w=>view w.wg=initial) (fun _=>True) (RxHistory.batchItem d cqes item) := by
  have safe : ∀ h (w : World),view w.wg=initial→(fun _ : List RxHistory.Event=>True) h := fun _ _ _=>True.intro
  have store : ∀ h (w v : World), productStoreView v=productStoreView w→
      (fun _ : List RxHistory.Event=>view w.wg=initial) h→view v.wg=initial :=
    fun _ _ _ same hi=>(product_view_transport same).trans hi
  cases item <;> unfold RxHistory.batchItem
  all_goals repeat' first
    | (environment_at "xmitMulticastLoopAudit"; exact multicast_structure initial _ _)
    | (current_env_at wgXmitPrefix; exact xmit_structure initial _ _ _ _)
    | (current_env_at wgReceivePrefix; exact receive_structure initial _ _)
    | (traffic_head RxHistory.pollScheduledInline; exact inline_structure initial)
    | (traffic_head Env.xmitPackets; exact viewLiftPrefix_preserves productStoreView safe store (xmitPackets_sameKernel _ _ _ _))
    | traffic_preserve_source safe using store

theorem batch_structure (initial) (items : List Env.BatchItem) :
    PrefixPreserves (fun _ w=>view w.wg=initial) (fun _=>True) (RxHistory.batch items) := by
  rw [TrafficSource.batch_factor]
  exact TrafficSource.batch_preserves (fun _ _ _=>True.intro)
    (fun _ _ _ same hi=>(product_view_transport same).trans hi) _ _
    (batchItem_structure initial) (afterBatch_structure initial) items

end Leanux.Proofs.WG.Queues.RxCredits.BaseCoherence
