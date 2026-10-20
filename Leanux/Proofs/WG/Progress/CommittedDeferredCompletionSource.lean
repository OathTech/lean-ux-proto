import Leanux.Proofs.WG.Progress.CommittedDeferredSource
import Leanux.Proofs.WG.Progress.CommittedCompletionSource

/-! Normal completion of the existing actual committed-run journal. The safe
predicate on stopped histories is True; no failed receipt is hidden. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.CommittedRuns.Deferred.Completion
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues Configuration
open RxHistory.DeferredSource

theorem atoms : AtomContracts (fun h _=>NormalHistory h) (fun _=>True) (fun {_} a=>old a) := by
  constructor
  all_goals intros; exact (Leanux.Proofs.WG.Progress.CommittedRuns.Completion.lift_preserves) _

theorem crypt_preserves : PrefixPreserves (fun h _=>NormalHistory h) (fun _=>True) crypt :=
  RxHistory.DeferredSource.crypt_preserves
    (I := fun h _=>NormalHistory h) (S := fun _=>True) (fun _ _ _=>True.intro) (fun _ _ _ _ h=>h)
    _ ((Leanux.Proofs.WG.Progress.CommittedRuns.Completion.schedule_preserves) none)

theorem send_preserves : PrefixPreserves (fun h _=>NormalHistory h) (fun _=>True) send :=
  RxHistory.DeferredSource.send_preserves
    (I := fun h _=>NormalHistory h) (S := fun _=>True) (fun _ _ _=>True.intro) (fun _ _ _ _ h=>h)
    _ (Leanux.Proofs.WG.Progress.CommittedRuns.Deferred.Completion.atoms) _ ((Leanux.Proofs.WG.Progress.CommittedRuns.Completion.schedule_preserves) none)

theorem afterXmit_preserves : PrefixPreserves (fun h _=>NormalHistory h) (fun _=>True) afterXmit :=
  RxHistory.DeferredSource.afterXmit_preserves
    (I := fun h _=>NormalHistory h) (S := fun _=>True) (fun _ _ _=>True.intro) (fun _ _ _ _ h=>h)
    _ (Leanux.Proofs.WG.Progress.CommittedRuns.Deferred.Completion.atoms) _ (Leanux.Proofs.WG.Progress.CommittedRuns.Deferred.Completion.crypt_preserves) _ (Leanux.Proofs.WG.Progress.CommittedRuns.Deferred.Completion.send_preserves)

theorem timers_preserves (j : UInt64) :
    PrefixPreserves (fun h _=>NormalHistory h) (fun _=>True) (timers j) :=
  RxHistory.DeferredSource.timers_preserves
    (I := fun h _=>NormalHistory h) (S := fun _=>True) (fun _ _ _=>True.intro) (fun _ _ _ _ h=>h)
    _ (Leanux.Proofs.WG.Progress.CommittedRuns.Deferred.Completion.atoms) _ (Leanux.Proofs.WG.Progress.CommittedRuns.Deferred.Completion.crypt_preserves) j

theorem placeholder_preserves (j : UInt64) :
    PrefixPreserves (fun h _=>NormalHistory h) (fun _=>True) (placeholder j) :=
  RxHistory.DeferredSource.placeholder_preserves
    (I := fun h _=>NormalHistory h) (S := fun _=>True) (fun _ _ _=>True.intro) (fun _ _ _ _ h=>h)
    _ (Leanux.Proofs.WG.Progress.CommittedRuns.Deferred.Completion.atoms) _ (Leanux.Proofs.WG.Progress.CommittedRuns.Deferred.Completion.crypt_preserves) _ (Leanux.Proofs.WG.Progress.CommittedRuns.Deferred.Completion.send_preserves) j

theorem idle_preserves : PrefixPreserves (fun h _=>NormalHistory h) (fun _=>True) idle :=
  RxHistory.DeferredSource.idle_preserves
    (I := fun h _=>NormalHistory h) (S := fun _=>True) (fun _ _ _=>True.intro) (fun _ _ _ _ h=>h)
    _ (Leanux.Proofs.WG.Progress.CommittedRuns.Deferred.Completion.atoms) _ (Leanux.Proofs.WG.Progress.CommittedRuns.Deferred.Completion.timers_preserves) _ (Leanux.Proofs.WG.Progress.CommittedRuns.Deferred.Completion.placeholder_preserves)

theorem afterAdvance_preserves : PrefixPreserves (fun h _=>NormalHistory h) (fun _=>True) afterAdvance :=
  RxHistory.DeferredSource.afterAdvance_preserves
    (I := fun h _=>NormalHistory h) (S := fun _=>True) (fun _ _ _=>True.intro) (fun _ _ _ _ h=>h)
    _ (Leanux.Proofs.WG.Progress.CommittedRuns.Deferred.Completion.atoms) _ (Leanux.Proofs.WG.Progress.CommittedRuns.Deferred.Completion.timers_preserves) _ (Leanux.Proofs.WG.Progress.CommittedRuns.Deferred.Completion.placeholder_preserves)

theorem deferred_preserves (call : EnvDeferredCall) :
    PrefixPreserves (fun h _=>NormalHistory h) (fun _=>True) (deferred call) :=
  RxHistory.DeferredSource.deferred_preserves _ (Leanux.Proofs.WG.Progress.CommittedRuns.Deferred.Completion.atoms) _ _ _ _ _ _ _
    (Leanux.Proofs.WG.Progress.CommittedRuns.Deferred.Completion.crypt_preserves) (Leanux.Proofs.WG.Progress.CommittedRuns.Deferred.Completion.send_preserves) (Leanux.Proofs.WG.Progress.CommittedRuns.Deferred.Completion.afterXmit_preserves) (Leanux.Proofs.WG.Progress.CommittedRuns.Deferred.Completion.timers_preserves) (Leanux.Proofs.WG.Progress.CommittedRuns.Deferred.Completion.placeholder_preserves)
    (Leanux.Proofs.WG.Progress.CommittedRuns.Deferred.Completion.idle_preserves) (Leanux.Proofs.WG.Progress.CommittedRuns.Deferred.Completion.afterAdvance_preserves) call

end Leanux.Proofs.WG.Progress.CommittedRuns.Deferred.Completion
