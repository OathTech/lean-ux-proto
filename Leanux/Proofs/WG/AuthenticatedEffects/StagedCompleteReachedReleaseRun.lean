import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedRelease

/-! A projected release cut reconstructs the original, named release
callback failure. The successful cut before a failed finish remains explicit;
no arbitrary monadic factor is introduced. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity RetirementSecurity
open TransmitSecurity.Staged.Obligations StagedTerminalComplete CompleteCarrier
open AllocatedObligation AllocatedObligation.CompletionBatch
open AllocatedObligation.CompletionBatch.Converse PeerRelease

theorem ReleaseProjection.run
    (projection : ReleaseProjection context phase ledger debts peer w history reason last saved) :
    runPrefix (Admission.actualOps.release peer) w history = (.error reason,last) := by
  cases projection with
  | cutStopped _ failed => rw [actual_run,failed]
  | finishStopped value g a cutHistory after performed _ _ _ _ _ failed =>
    rw [actual_run,performed]
    exact failed

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached
