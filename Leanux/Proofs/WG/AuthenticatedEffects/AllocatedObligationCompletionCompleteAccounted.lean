import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationCompletionCompleteFrontier
import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntryCompleteCarrier

/-! A stopped completion exposes an accounted saved native cut. The actual
failed run and its source settlement chain remain in the original frontier;
the saved world is not asserted to be a returned world of a stopped action. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.CompletionBatch.Converse
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity
open TransmitSecurity.Staged.Obligations StagedTerminalComplete StagedEntry.CompleteCarrier

theorem indexed_frontier_accounted
    (frontier : IndexedFrontier context ledger debts reason history)
    (complete : Complete history ledger) :
    Accounted history ledger debts
      (⟨.selected,context.pid,frontier.phase.active context⟩ :: context.locals) frontier.world.wg := by
  obtain ⟨suffix,grown⟩ := frontier.prefixHistory
  have same := (congrArg (List.filterMap ledgerEvent?) grown).trans frontier.lastCut
  rw [List.filterMap_append] at same
  have empty : suffix.filterMap ledgerEvent? = [] :=
    List.append_cancel_left (as := frontier.before.filterMap ledgerEvent?)
      (by simpa only [List.append_nil] using same)
  refine ⟨?_,complete⟩
  simpa only [grown] using StagedEntry.Queued.Inv.history frontier.owned.entry suffix
    (fun event member => ledger_quiet_birth event (List.filterMap_eq_nil_iff.mp empty event member))

theorem indexed_stopped_accounted
    (stopped : IndexedStopped context ledger debts reason history)
    (complete : Complete history ledger) :
    ∃ frontier : IndexedFrontier context ledger debts reason history,
      Accounted history ledger debts
        (⟨.selected,context.pid,frontier.phase.active context⟩ :: context.locals) frontier.world.wg := by
  obtain ⟨frontier⟩ := stopped
  exact ⟨frontier,indexed_frontier_accounted frontier complete⟩

theorem ReleaseStopped.accounted
    (frontier : ReleaseStopped context phase ledger debts peer w history reason last) :
    ∃ after locals cut, Staged.Obligations.Step ledger after ∧ Accounted last after debts locals cut := by
  cases frontier with
  | cutStopped owned failed complete =>
    have entry := Source.cut_entry_history peer w.ambient owned.entry
    rw [failed] at entry
    exact ⟨ledger,_,w.wg,.refl _,entry,complete⟩
  | finishStopped value g a cutHistory after _ step _ _ owned complete failed =>
    have same := PeerRelease.finish_history value {w with wg := g,ambient := a}
      (cutHistory ++ [PeerRelease.receipt peer value w.wg g w.ambient a])
    rw [failed] at same
    change last = _ at same
    exact ⟨after,_,g,step,(by simpa only [same] using owned.entry),complete⟩

theorem DisposeStopped.accounted
    (frontier : DisposeStopped context key ledger reason last) :
    ∃ after locals cut, Staged.Obligations.Step ledger after ∧ Accounted last after [] locals cut := by
  cases frontier with
  | keyStopped _ _ _ _ stopped complete =>
    obtain ⟨saved,accounted⟩ := indexed_stopped_accounted stopped complete
    exact ⟨ledger,_,saved.world.wg,.refl _,accounted⟩
  | peerStopped _ _ _ stopped => exact stopped.accounted

theorem BatchStopped.accounted
    (frontier : BatchStopped context ledger key w history reason last) :
    ∃ after debts locals cut,
      Staged.Obligations.Step ledger after ∧ Accounted last after debts locals cut := by
  cases frontier with
  | sending _ stopped =>
    obtain ⟨after,debts,trace,stopped,complete⟩ := stopped
    obtain ⟨saved,accounted⟩ := indexed_stopped_accounted stopped complete
    exact ⟨after,debts,_,saved.world.wg,trace.step,accounted⟩
  | disposing _ _ _ _ _ trace _ _ _ _ stopped =>
    obtain ⟨after,locals,cut,step,accounted⟩ := stopped.accounted
    exact ⟨after,[],locals,cut,trace.step.trans step,accounted⟩

/-- The original worker frontier, including actual failed runs and chosen
settlements, accompanies the accounted cut used by the outer Stop carrier. -/
theorem worker_stopped_accounted
    (frontier : WorkerFailure ledger locals pid items head w history reason last) :
    WorkerFailure ledger locals pid items head w history reason last ∧
    ∃ after debts active cut,
      Staged.Obligations.Step ledger after ∧ Accounted last after debts active cut := by
  refine ⟨frontier,?_⟩
  obtain ⟨context,_,_,_,_,_,_,_,stopped⟩ := frontier
  exact stopped.accounted

end Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.CompletionBatch.Converse
