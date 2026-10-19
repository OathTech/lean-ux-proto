import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationCompletionCompleteWorker

/-! Extract terminal completeness from the actual stopped completion
frontier. The successor comes from its retained source settlement chain;
this is not an implication from an arbitrary ledger Step. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.CompletionBatch.Converse
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity
open TransmitSecurity.Staged.Obligations StagedTerminalComplete

theorem ReleaseStopped.complete
    (frontier : ReleaseStopped context phase ledger debts peer w history reason last) :
    ∃ after, Staged.Obligations.Step ledger after ∧ Complete last after := by
  cases frontier with
  | cutStopped _ _ complete => exact ⟨ledger,.refl _,complete⟩
  | finishStopped _ _ _ _ after _ step _ _ _ complete _ => exact ⟨after,step,complete⟩

theorem DisposeStopped.complete
    (frontier : DisposeStopped context key ledger reason last) :
    ∃ after, Staged.Obligations.Step ledger after ∧ Complete last after := by
  cases frontier with
  | keyStopped _ _ _ _ _ complete => exact ⟨ledger,.refl _,complete⟩
  | peerStopped _ _ _ released => exact released.complete

theorem BatchStopped.complete
    (frontier : BatchStopped context ledger key w history reason last) :
    ∃ after, Staged.Obligations.Step ledger after ∧ Complete last after := by
  cases frontier with
  | sending _ stopped =>
    obtain ⟨after,debts,trace,_,complete⟩ := stopped
    exact ⟨after,trace.step,complete⟩
  | disposing _ _ _ _ _ trace _ _ _ _ stopped =>
    obtain ⟨after,step,complete⟩ := stopped.complete
    exact ⟨after,trace.step.trans step,complete⟩

theorem worker_stopped_complete
    (frontier : WorkerFailure ledger locals pid items head w history reason last) :
    ∃ after, Staged.Obligations.Step ledger after ∧ Complete last after := by
  obtain ⟨context,_,_,_,_,_,_,_,stopped⟩ := frontier
  exact stopped.complete

end Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.CompletionBatch.Converse
