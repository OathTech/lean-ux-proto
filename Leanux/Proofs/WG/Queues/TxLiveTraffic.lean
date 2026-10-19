import Leanux.Proofs.WG.Queues.TxLiveDeferred

/-! Full original inject, flood and batch callers, including committed crypt,
send, inline NAPI and post-batch waits, preserve the logical encryption
frontier and its physical refinement on normal return. -/
namespace Leanux.Proofs.WG.Queues.TxDisposition.LiveTraffic
open Leanux Leanux.WG Leanux.Env Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do
open LiveFrontier RxCredits

theorem drained_observed (what : String) (flags : List Bool) :
    PrefixPreserves LiveScheduler.Inv (fun _=>True)
      (RxHistory.mixed (requireDrainedPrefix what flags)) :=
  observed _ _ (Appends.focus _ _ _)
    (RxHistory.mixed_erases (requireDrainedPrefix_erases what flags)) (LiveDeferred.drained what flags)

theorem inject (family port : Nat) (msg : List UInt8) (tos : Nat) (ll : Bool) (dest : Nat) :
    PrefixPreserves LiveScheduler.Inv (fun _=>True) (RxHistory.inject family port msg tos ll dest) := by
  rw [TrafficSource.inject_factor]
  exact TrafficSource.inject_preserves (I:=LiveScheduler.Inv)
    (fun _ _ _=>True.intro) (fun _ _ _ eq hi=>product_store eq hi) _ _ _
    LiveIngress.receive_observed LiveDeferred.crypt drained_observed family port msg tos ll dest

theorem afterBatch : PrefixPreserves LiveScheduler.Inv (fun _=>True) RxHistory.afterBatch := by
  rw [TrafficSource.afterBatch_factor]
  exact TrafficSource.afterBatch_preserves (I:=LiveScheduler.Inv)
    (fun _ _ _=>True.intro) (fun _ _ _ eq hi=>product_store eq hi) _ _ _ _ _
    LiveDeferred.crypt LiveDeferred.send LiveDeferred.atoms.sendOne LiveScheduler.schedule drained_observed

theorem flood (count port family : Nat) (messages : List (List UInt8)) :
    PrefixPreserves LiveScheduler.Inv (fun _=>True) (RxHistory.flood count port family messages) := by
  rw [TrafficSource.flood_factor]
  exact TrafficSource.flood_preserves (I:=LiveScheduler.Inv)
    (fun _ _ _=>True.intro) (fun _ _ _ eq hi=>product_store eq hi) _ _ _ _
    LiveIngress.receive_observed LiveNapi.inline_observed afterBatch drained_observed count port family messages

theorem batch (items : List BatchItem) :
    PrefixPreserves LiveScheduler.Inv (fun _=>True) (RxHistory.batch items) := by
  rw [TrafficSource.batch_factor]
  exact TrafficSource.batch_preserves (I:=LiveScheduler.Inv)
    (fun _ _ _=>True.intro) (fun _ _ _ eq hi=>product_store eq hi) _ _ batch_item afterBatch items

theorem inject_native (family port : Nat) (msg : List UInt8) (tos : Nat) (ll : Bool) (dest : Nat) :
    Preserves (fun w : World=>Ready w.wg) (Env.inject family port msg tos ll dest) :=
  native _ _ (RxHistory.inject_erases family port msg tos ll dest) (inject family port msg tos ll dest)

theorem afterBatch_native : Preserves (fun w : World=>Ready w.wg) Env.afterBatch :=
  native _ _ RxHistory.afterBatch_erases afterBatch

theorem flood_native (count port family : Nat) (messages : List (List UInt8)) :
    Preserves (fun w : World=>Ready w.wg) (Env.flood count port family messages) :=
  native _ _ (RxHistory.flood_erases count port family messages) (flood count port family messages)

theorem batch_native (items : List BatchItem) :
    Preserves (fun w : World=>Ready w.wg) (Env.batch items) :=
  native _ _ (RxHistory.batch_erases items) (batch items)

end Leanux.Proofs.WG.Queues.TxDisposition.LiveTraffic
