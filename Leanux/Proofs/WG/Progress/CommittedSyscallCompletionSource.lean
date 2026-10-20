import Leanux.Proofs.WG.Progress.CommittedSyscallSource
import Leanux.Proofs.WG.Progress.CommittedTrafficCompletionSource

/-! Normal completion of the existing actual committed-run journal. The safe
predicate on stopped histories is True; no failed receipt is hidden. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.CommittedRuns.Syscalls.Completion
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues Configuration
open RxHistory.DeferredSource

theorem observe_preserves :
    PrefixPreserves (fun h _ => NormalHistory h) (fun _ => True) observe := by
  apply (Leanux.Proofs.WG.Progress.CommittedRuns.Traffic.Completion.observe_preserves).bind
  rintro ⟨ret,result⟩
  apply ((Leanux.Proofs.WG.Progress.CommittedRuns.Completion.lift_preserves) _).bind
  intro _
  exact Roaming.RemoteOuterRules.socket (fun h _=>NormalHistory h) (fun _=>True) (fun _ _ _=>True.intro)
    (fun _ => (Leanux.Proofs.WG.Progress.CommittedRuns.Completion.lift_preserves) _) _ _ (PrefixPreserves.pure (I:=fun h _=>NormalHistory h) (S:=fun _=>True) (fun _ _ _=>True.intro) ret)

theorem dispatch_preserves (call : Syscall) :
    PrefixPreserves (fun h _=>NormalHistory h) (fun _=>True) (dispatch call) := by
  apply dispatchWith_preserves
  · intro _ _; exact (Leanux.Proofs.WG.Progress.CommittedRuns.Completion.lift_preserves) _
  · intro _; exact (Leanux.Proofs.WG.Progress.CommittedRuns.Completion.lift_preserves) _
  · exact (Leanux.Proofs.WG.Progress.CommittedRuns.Completion.lift_preserves) _
  · exact (Leanux.Proofs.WG.Progress.CommittedRuns.Completion.lift_preserves) _
  · intro _ _ _ _; exact (Leanux.Proofs.WG.Progress.CommittedRuns.Completion.lift_preserves) _
  · intro family port msg tos ll dest
    exact Roaming.RemoteOuterRules.socket (fun h _=>NormalHistory h) (fun _=>True) (fun _ _ _=>True.intro)
      (fun _ => (Leanux.Proofs.WG.Progress.CommittedRuns.Completion.lift_preserves) _) _ _ ((Leanux.Proofs.WG.Progress.CommittedRuns.Traffic.Completion.inject_preserves) family port msg tos ll dest)
  · exact (Leanux.Proofs.WG.Progress.CommittedRuns.Traffic.Completion.flood_preserves)
  · exact (Leanux.Proofs.WG.Progress.CommittedRuns.Traffic.Completion.batch_preserves)
  · exact (Leanux.Proofs.WG.Progress.CommittedRuns.Syscalls.Completion.observe_preserves)

theorem syscall_preserves (call : Syscall) :
    PrefixPreserves (fun h _=>NormalHistory h) (fun _=>True) (syscall call) :=
  SyscallSource.preserves (I:=fun h _=>NormalHistory h) (S:=fun _=>True) (fun _ _ _=>True.intro) (fun _ _ _ _ hi=>hi) call _ _ _ _ _ _ _
    ((Leanux.Proofs.WG.Progress.CommittedRuns.Syscalls.Completion.dispatch_preserves) call) (Leanux.Proofs.WG.Progress.CommittedRuns.Deferred.Completion.send_preserves) (Leanux.Proofs.WG.Progress.CommittedRuns.Deferred.Completion.idle_preserves)
    ((Leanux.Proofs.WG.Progress.CommittedRuns.Completion.lift_preserves) _) (Leanux.Proofs.WG.Progress.CommittedRuns.Deferred.Completion.afterXmit_preserves) (Leanux.Proofs.WG.Progress.CommittedRuns.Deferred.Completion.afterAdvance_preserves)
    ((Leanux.Proofs.WG.Progress.CommittedRuns.Completion.lift_preserves) _)

end Leanux.Proofs.WG.Progress.CommittedRuns.Syscalls.Completion
