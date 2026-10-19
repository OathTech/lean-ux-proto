import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedWorkerCompletionWorker

/-! The reached account retains its fixed native worker prefix and the
same matched source cut. Caller locals and cleanup debts are projected from
that cut, rather than chosen by a separate endpoint existence theorem. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.WorkerCompletion
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity RetirementSecurity
open TransmitSecurity.Staged.Obligations StagedTerminalComplete CompleteCarrier
open AllocatedObligation CompletionBatch

theorem SelectedCut.accounted
    (result : SelectedCut ledger locals pid w history items head u middle reason last) :
    ∃ context : Context, context.pid = pid ∧ context.locals = locals ∧ context.items = items ∧
      context.initialLedger = ledger ∧
      ∃ point, ∃ saved : Cut context,
        Matched context ledger u middle reason last point saved ∧
        runPrefix (sourcePrefix pid point) w history = (.ok ((),saved.world),saved.before) ∧
        Staged.Obligations.Step ledger saved.ledger ∧ saved.Valid reason last ∧
        Accounted last saved.ledger saved.debts
          (⟨.selected,pid,saved.phase.active context⟩ :: locals) saved.world.wg := by
  obtain ⟨context,peer,localEq,batch,initial,_,_,_,_,_,point,saved,matched,reached,valid⟩ := result
  refine ⟨context,peer,localEq,batch,initial,point,saved,matched,reached,matched_step matched,valid,?_⟩
  simpa only [Cut.locals,peer,localEq] using valid.accounted

/-- A supplied actual selection path suffices; the original native worker
failure chooses the complete scoped callback's matching account and prefix. -/
theorem selected_accounted_cut
    (path : SelectionPath ledger locals pid w history ⟨items,head,true⟩ u middle)
    (failed : runPrefix (CausalJournal.transmit pid) w history = (.error reason,last)) :
    SelectedCut ledger locals pid w history items head u middle reason last ∧
    ∃ context : Context, context.pid = pid ∧ context.locals = locals ∧ context.items = items ∧
      context.initialLedger = ledger ∧
      ∃ point, ∃ saved : Cut context,
        Matched context ledger u middle reason last point saved ∧
        runPrefix (sourcePrefix pid point) w history = (.ok ((),saved.world),saved.before) ∧
        Staged.Obligations.Step ledger saved.ledger ∧ saved.Valid reason last ∧
        Accounted last saved.ledger saved.debts
          (⟨.selected,pid,saved.phase.active context⟩ :: locals) saved.world.wg := by
  have result := selected_failure path failed
  exact ⟨result,result.accounted⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.WorkerCompletion
