import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedCleanup

/-! Every retained cleanup snapshot is tied to an actual prefix of the
same fixed native free list. No arbitrary prefix action or factorization is
quantified over, and active ownership is the exact remaining suffix. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity RetirementSecurity
open TransmitSecurity.Staged.Obligations StagedTerminalComplete CompleteCarrier
open AllocatedObligation AllocatedObligation.CompletionBatch

/-- The account at every completed free-list prefix has a native source
run from the exact caller entry, and retains the remaining cleanup path. -/
theorem CleanupPath.split (front : List SkbId)
    (path : CleanupPath context ledger (front ++ rest) debts w history v last) :
    ∃ cutWorld cutHistory cutDebts,
      runPrefix (freeLoop cleanupOps front) w history = (.ok ((),cutWorld),cutHistory) ∧
      Owned context (.freeing rest) cutHistory ledger cutDebts cutWorld ∧
      Complete cutHistory ledger ∧
      CleanupPath context ledger rest cutDebts cutWorld cutHistory v last := by
  induction front generalizing debts w history with
  | nil =>
    exact ⟨w,history,debts,rfl,path.initial.1,path.initial.2,path⟩
  | cons skb front ih =>
    cases path with
    | next owned complete generation epoch performed tail =>
      obtain ⟨cutWorld,cutHistory,cutDebts,prefixRun,atCut,paired,remaining⟩ := ih tail
      refine ⟨cutWorld,cutHistory,cutDebts,?_,atCut,paired,remaining⟩
      change runPrefix (FirstTerminal.cleanupFree skb >>= fun _ => freeLoop cleanupOps front) w history = _
      rw [runPrefix_bind,performed]
      exact prefixRun

theorem CleanupPath.accounted_cut (front : List SkbId)
    (path : CleanupPath context ledger (front ++ rest) debts w history v last) :
    ∃ cutWorld cutHistory cutDebts,
      runPrefix (freeLoop cleanupOps front) w history = (.ok ((),cutWorld),cutHistory) ∧
      Accounted cutHistory ledger cutDebts
        (⟨.selected,context.pid,rest⟩ :: context.locals) cutWorld.wg := by
  obtain ⟨cutWorld,cutHistory,cutDebts,prefixRun,owned,complete,_⟩ := path.split front
  exact ⟨cutWorld,cutHistory,cutDebts,prefixRun,owned.entry,complete⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached
