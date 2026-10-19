import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedRepayment

/-! The original disposal caller retains its exact cleanup path and the
subsequent reference repayments. Its input state is the caller's state, not an
existential replacement; all intermediate states are outputs of named native
source calls. Global provenance of that input remains a separate obligation. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity RetirementSecurity
open TransmitSecurity.Staged.Obligations StagedTerminalComplete CompleteCarrier
open AllocatedObligation AllocatedObligation.CompletionBatch
open AllocatedObligation.CompletionBatch.Converse HandshakeSecurity.StagedDisposal

def DisposalInterval (context : Context) (ledger : Ledger) (debts : List CleanupDebt)
    (key : KeypairId) (w : World) (history : List CausalJournal.Event)
    (result : Except Stop (Bool × World)) (last : List CausalJournal.Event) : Prop :=
  ∃ freeWorld freeHistory,
    CleanupPath context ledger context.items debts w history freeWorld freeHistory ∧
    runPrefix (CompletionBatch.release cleanupOps context.pid key) freeWorld freeHistory = (result,last) ∧
    match result with
    | .error reason => ∃ saved,
        RepaymentStopped context ledger key freeWorld freeHistory reason last saved
    | .ok (value,v) => RepaymentReturned context ledger key freeWorld freeHistory last value v

/-- No disposal-success or free-success premise is assumed. The concrete
input ownership derives every free, then the original key/peer sequence is
executed from that same output, including its actual stopped suffix. -/
theorem disposal_interval (key : KeypairId)
    (before : Owned context (.freeing context.items) history ledger debts w)
    (localDebts : LocalDebts context context.items debts) (complete : Complete history ledger) :
    DisposalInterval context ledger debts key w history
      (runPrefix (CausalJournal.completionOps.dispose context.pid context.items key) w history).1
      (runPrefix (CausalJournal.completionOps.dispose context.pid context.items key) w history).2 := by
  obtain ⟨freeWorld,freeHistory,path⟩ := cleanup_path context.items before localDebts complete
  have source : runPrefix (CausalJournal.completionOps.dispose context.pid context.items key) w history =
      runPrefix (CompletionBatch.release cleanupOps context.pid key) freeWorld freeHistory := by
    change runPrefix (TxSource.dispose cleanupOps context.pid context.items key) w history = _
    rw [← dispose_factor]
    change runPrefix (freeLoop cleanupOps context.items >>= fun _ => _) w history = _
    rw [runPrefix_bind,path.run]
  rw [source]
  refine ⟨freeWorld,freeHistory,path,Prod.ext rfl rfl,?_⟩
  have checked := repayment_cases key path.returned.1 path.returned.2
  cases performed : runPrefix (CompletionBatch.release cleanupOps context.pid key) freeWorld freeHistory with
  | mk result last =>
    cases result <;> simpa only [performed] using checked

theorem DisposalInterval.run
    (interval : DisposalInterval context ledger debts key w history result last) :
    runPrefix (CausalJournal.completionOps.dispose context.pid context.items key) w history = (result,last) := by
  obtain ⟨freeWorld,freeHistory,path,performed,_⟩ := interval
  change runPrefix (TxSource.dispose cleanupOps context.pid context.items key) w history = _
  rw [← dispose_factor]
  change runPrefix (freeLoop cleanupOps context.items >>= fun _ => _) w history = _
  rw [runPrefix_bind,path.run]
  exact performed

/-- The actual stopped disposition has a matching cut and ledger account,
and retains the path from the exact disposal entry through every free. -/
theorem DisposalInterval.stopped
    (interval : DisposalInterval context ledger debts key w history (.error reason) last) :
    ∃ freeWorld freeHistory saved,
      CleanupPath context ledger context.items debts w history freeWorld freeHistory ∧
      RepaymentStopped context ledger key freeWorld freeHistory reason last saved ∧
      Staged.Obligations.Step ledger saved.ledger ∧ saved.Valid reason last := by
  obtain ⟨freeWorld,freeHistory,path,_,saved,stopped⟩ := interval
  exact ⟨freeWorld,freeHistory,saved,path,stopped,stopped.step,stopped.valid⟩

theorem DisposalInterval.returned
    (interval : DisposalInterval context ledger debts key w history (.ok (value,v)) last) :
    value = true ∧ ∃ after, Staged.Obligations.Step ledger after ∧
      Accounted last after [] context.locals v.wg := by
  obtain ⟨_,_,_,_,valueEq,_,_,_,_,_,released,g,a,cutHistory,after,
    _,_,step,_,_,owned,complete⟩ := interval
  exact ⟨valueEq,after,step,owned.finished_entry,complete⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached
