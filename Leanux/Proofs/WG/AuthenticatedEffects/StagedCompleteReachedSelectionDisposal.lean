import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedDequeueCuts

/-! Joining the original worker selection to the original crypted disposal
prefix. This closes that concrete caller interval, while Stops inside
sending and inside DEAD disposal keep their separate frontier obligations. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity RetirementSecurity
open TransmitSecurity.Staged.Obligations StagedTerminalComplete CompleteCarrier
open AllocatedObligation AllocatedObligation.CompletionBatch

def workerDisposalPrefix (pid : PeerId) (stage : RepaymentStage) : PrefixM CausalJournal.Event Unit := do
  let selected ← workerSelection pid
  match selected with
  | none => pure ()
  | some picked =>
    if picked.crypted then
      CompletionEffects.completeScoped CausalJournal.Event.scope CausalSources.Cause.completion
        CausalJournal.completionOps pid picked.items
      freeLoop cleanupOps picked.items
      repaymentPrefix pid picked.head.keypair stage
    else pure ()

theorem SelectionPath.disposal_run
    (path : SelectionPath ledger locals pid w history ⟨items,head,true⟩ u middle)
    (peer : context.pid = pid) (batch : context.items = items)
    (prefixRun : runPrefix (cryptedDisposalPrefix context head.keypair stage) u middle =
      (.ok ((),savedWorld),savedHistory)) :
    runPrefix (workerDisposalPrefix pid stage) w history = (.ok ((),savedWorld),savedHistory) := by
  rw [workerDisposalPrefix,runPrefix_bind,path.run]
  simpa only [cryptedDisposalPrefix,scopedCompletion,disposalPrefix,peer,batch,↓reduceIte] using prefixRun

/-- A crypted worker that stops after sending reaches its accounted cut
through the fixed original selection, send, cleanup and repayment prefix.
The same context, ledger successor and actual failed suffix remain linked.
A sending-internal Stop is reported separately rather than promoted. -/
theorem SelectionPath.crypted_reached_cut
    (path : SelectionPath ledger locals pid w history ⟨items,head,true⟩ u middle)
    (interval : WorkerInterval ledger locals pid items head u middle (.error reason) last) :
    ∃ context : Context, context.pid = pid ∧ context.locals = locals ∧ context.items = items ∧
      context.initialLedger = ledger ∧
      ((runPrefix (scopedCompletion context) u middle = (.error reason,last) ∧
        Converse.SendingStopped context ledger [] reason last) ∨
      ∃ stage, ∃ saved : Cut context,
        runPrefix (workerDisposalPrefix pid stage) w history = (.ok ((),saved.world),saved.before) ∧
        Staged.Obligations.Step ledger saved.ledger ∧ saved.Valid reason last) := by
  obtain ⟨context,peer,localEq,batch,initial,_,_,_,interval⟩ := interval
  refine ⟨context,peer,localEq,batch,initial,?_⟩
  cases interval.stopped_cut with
  | inl failed => exact .inl failed
  | inr reached =>
    obtain ⟨stage,saved,prefixRun,step,valid⟩ := reached
    exact .inr ⟨stage,saved,path.disposal_run peer batch prefixRun,step,valid⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached
