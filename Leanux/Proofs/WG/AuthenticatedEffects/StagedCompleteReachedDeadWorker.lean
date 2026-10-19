import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedDeadCleanup

/-! The DEAD repayment cut is reached from the actual worker entry through
its fixed peek, readiness, dequeue, guard and cleanup prefix. The outer
initialized entry anchor remains an explicit separate obligation. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity RetirementSecurity
open TransmitSecurity.Staged.Obligations StagedTerminalComplete CompleteCarrier
open AllocatedObligation AllocatedObligation.CompletionBatch HandshakeSecurity.StagedConservation

theorem SelectionPath.dead_prefix_run
    (path : SelectionPath ledger locals pid w history ⟨items,head,false⟩ u middle)
    (performed : runPrefix (deadPrefix pid items head stage) u middle = (.ok ((),v),last)) :
    runPrefix (workerDeadPrefix pid stage) w history = (.ok ((),v),last) := by
  rw [workerDeadPrefix,runPrefix_bind,path.run]
  exact performed

theorem SelectionPath.dead_reached_cut
    (path : SelectionPath ledger locals pid w history ⟨items,head,false⟩ u middle)
    (frontier : Converse.Dead.Stopped ledger [] locals pid items head u middle reason last) :
    ∃ freeWorld freeHistory afterFree,
      DeadCleanupPath ledger [] locals pid items head u middle freeWorld freeHistory afterFree ∧
      ∃ stage, ∃ cut : DeadCut,
        runPrefix (workerDeadPrefix pid stage) w history = (.ok ((),cut.world),cut.before) ∧
        Staged.Obligations.Step ledger cut.ledger ∧ cut.debts = [] ∧ cut.locals = locals ∧
        cut.Valid reason last := by
  obtain ⟨freeWorld,freeHistory,afterFree,cleanup,stage,cut,performed,step,debtEq,localEq,valid⟩ :=
    dead_stopped_cut path.accounted_entry.1 frontier
  exact ⟨freeWorld,freeHistory,afterFree,cleanup,stage,cut,path.dead_prefix_run performed,
    step,debtEq,localEq,valid⟩

/-- Original worker failure after a DEAD selection retains the actual
cleanup path and a matched repayment cut. The selected prefix itself
derives the pending batch; no completed-caller or drain premise is used. -/
theorem SelectionPath.dead_worker_stopped_cut
    (path : SelectionPath ledger locals pid w history ⟨items,head,false⟩ u middle)
    (failed : runPrefix (CausalJournal.transmit pid) w history = (.error reason,last)) :
    Converse.Dead.Stopped ledger [] locals pid items head u middle reason last ∧
      ∃ freeWorld freeHistory afterFree,
        DeadCleanupPath ledger [] locals pid items head u middle freeWorld freeHistory afterFree ∧
        ∃ stage, ∃ cut : DeadCut,
          runPrefix (workerDeadPrefix pid stage) w history = (.ok ((),cut.world),cut.before) ∧
          Staged.Obligations.Step ledger cut.ledger ∧ cut.debts = [] ∧ cut.locals = locals ∧
          cut.Valid reason last := by
  rw [path.callback_run] at failed
  change runPrefix (Terminal.deadObserved CausalJournal.txEvent CausalJournal.txEvent?
    CausalJournal.Event.stagedDisposal CausalJournal.Event.terminalDrop pid items head) u middle = _ at failed
  have frontier := Converse.Dead.dead_cases pid items head path.accounted_entry.1 path.accounted_entry.2
  rw [failed] at frontier
  exact ⟨frontier,path.dead_reached_cut frontier⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached
