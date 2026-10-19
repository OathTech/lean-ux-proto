import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedDispatchSource

/-! Native dispatch accounts are derived from initialization along the fixed
source path. No incoming ledger, caller carrier or global safety is assumed. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.RunnerSource
open Leanux Leanux.WG Leanux.Runner Leanux.Proofs.Logged
open Queues Queues.RxCredits TransmitSecurity CompleteRunner

theorem DispatchPath.entry
    (path : DispatchPath trace placeholders count op state world history) :
    CompletePrefix.With CompleteRunner.DeleteFrames.Entry CompleteProduct.Safe history world := by
  have prepared := prepared_entry trace placeholders count path.completed
  have before : CompletePrefix.With CompleteRunner.DeleteFrames.Entry CompleteProduct.Safe
      path.prior (RunnerOperation.prepare trace state) :=
    ⟨⟨prepared.1.1,prepared.1.2.1,prepared.1.2.2.1⟩,prepared.2⟩
  obtain ⟨_,_,_,after⟩ := SyscallSource.enter_checked (callAt state op)
    (RunnerOperation.prepare trace state) path.prior before
  simpa only [path.entered] using after

/-- The account's world is the actual initialized, source-selected dispatch
world. Its native ownership and cleanup predicates refer to that same state. -/
theorem DispatchPath.accounted
    (path : DispatchPath trace placeholders count op state world history) :
    ∃ ledger, CompleteCarrier.Accounted history ledger [] [] world.wg :=
  path.entry.1.1.1

theorem DispatchPath.cut
    (path : DispatchPath trace placeholders count op state world history) :
    ∃ ledger, CompleteConsequences.Cut history ledger [] [] world.wg := by
  obtain ⟨ledger,before⟩ := path.accounted
  exact ⟨ledger,CompleteConsequences.accounted before⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.RunnerSource
