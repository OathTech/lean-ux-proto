import Leanux.Proofs.WG.Progress.CommittedTrafficSource
import Leanux.Proofs.WG.Progress.CommittedDeferredCompletionSource

/-! Normal completion of the existing actual committed-run journal. The safe
predicate on stopped histories is True; no failed receipt is hidden. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.CommittedRuns.Traffic.Completion
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues Configuration
open RxHistory.DeferredSource

theorem inject_preserves (family port : Nat) (msg : List UInt8) (tos : Nat) (ll : Bool) (dest : Nat) :
    PrefixPreserves (fun h _=>NormalHistory h) (fun _=>True) (inject family port msg tos ll dest) :=
  TrafficSource.inject_preserves (I := fun h _=>NormalHistory h) (S := fun _=>True)
    (fun _ _ _=>True.intro) (fun _ _ _ _ h=>h) _ _ _
    (fun _ _=>(Leanux.Proofs.WG.Progress.CommittedRuns.Completion.lift_preserves) _) (Leanux.Proofs.WG.Progress.CommittedRuns.Deferred.Completion.crypt_preserves) (fun _ _=>(Leanux.Proofs.WG.Progress.CommittedRuns.Completion.lift_preserves) _)
    family port msg tos ll dest

theorem afterBatch_preserves :
    PrefixPreserves (fun h _=>NormalHistory h) (fun _=>True) afterBatch :=
  TrafficSource.afterBatch_preserves (I := fun h _=>NormalHistory h) (S := fun _=>True)
    (fun _ _ _=>True.intro) (fun _ _ _ _ h=>h) _ _ _ _ _
    (Leanux.Proofs.WG.Progress.CommittedRuns.Deferred.Completion.crypt_preserves) (Leanux.Proofs.WG.Progress.CommittedRuns.Deferred.Completion.send_preserves) ((Leanux.Proofs.WG.Progress.CommittedRuns.Deferred.Completion.deferred_preserves) .sendOne)
    (Leanux.Proofs.WG.Progress.CommittedRuns.Completion.schedule_preserves) (fun _ _=>(Leanux.Proofs.WG.Progress.CommittedRuns.Completion.lift_preserves) _)

theorem flood_preserves (count port family : Nat) (messages : List (List UInt8)) :
    PrefixPreserves (fun h _=>NormalHistory h) (fun _=>True) (flood count port family messages) :=
  TrafficSource.flood_preserves (I := fun h _=>NormalHistory h) (S := fun _=>True)
    (fun _ _ _=>True.intro) (fun _ _ _ _ h=>h) _ _ _ _
    (fun _ _=>(Leanux.Proofs.WG.Progress.CommittedRuns.Completion.lift_preserves) _) ((Leanux.Proofs.WG.Progress.CommittedRuns.Completion.lift_preserves) _) (Leanux.Proofs.WG.Progress.CommittedRuns.Traffic.Completion.afterBatch_preserves)
    (fun _ _=>(Leanux.Proofs.WG.Progress.CommittedRuns.Completion.lift_preserves) _) count port family messages

theorem batchItem_preserves  (device : Device) (cqes : List Int) (item : Env.BatchItem) :
    PrefixPreserves (fun h _=>NormalHistory h) (fun _=>True) (batchItem device cqes item) :=
  batchItemWith_preserves (I := fun h _=>NormalHistory h) (S := fun _=>True)
    (fun _ _ _=>True.intro) (fun _ _ _ _ h=>h) _ _ _ _
    (fun _ _=>(Leanux.Proofs.WG.Progress.CommittedRuns.Completion.lift_preserves) _) ((Leanux.Proofs.WG.Progress.CommittedRuns.Completion.lift_preserves) _) (fun _ _=>(Leanux.Proofs.WG.Progress.CommittedRuns.Completion.lift_preserves) _)
    (fun _ _ _ _=>(Leanux.Proofs.WG.Progress.CommittedRuns.Completion.lift_preserves) _) device cqes item

theorem batch_preserves (items : List Env.BatchItem) :
    PrefixPreserves (fun h _=>NormalHistory h) (fun _=>True) (batch items) :=
  TrafficSource.batch_preserves (I := fun h _=>NormalHistory h) (S := fun _=>True)
    (fun _ _ _=>True.intro) (fun _ _ _ _ h=>h) _ _ (Leanux.Proofs.WG.Progress.CommittedRuns.Traffic.Completion.batchItem_preserves) (Leanux.Proofs.WG.Progress.CommittedRuns.Traffic.Completion.afterBatch_preserves) items

theorem observe_preserves :
    PrefixPreserves (fun h _=>NormalHistory h) (fun _=>True) observe :=
  PrefixPreserves.bind (Leanux.Proofs.WG.Progress.CommittedRuns.Deferred.Completion.idle_preserves) (fun _=>(Leanux.Proofs.WG.Progress.CommittedRuns.Completion.lift_preserves) _)

end Leanux.Proofs.WG.Progress.CommittedRuns.Traffic.Completion
