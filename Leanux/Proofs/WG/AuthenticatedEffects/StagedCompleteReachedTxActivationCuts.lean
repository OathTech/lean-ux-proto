import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedTxActivationCases

/-! Fixed activation prefixes reach the same completion or reschedule cut.
The original worker classification and settlement ledger remain attached to
those runs. No world is reconstructed from a logical history predicate. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.TxActivation
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity RetirementSecurity
open TransmitSecurity.Staged.Obligations CompleteCarrier AllocatedObligation CompletionBatch

def workerPrefix (pid : PeerId) (point : WorkerCompletion.Point) : PrefixM CausalJournal.Event Unit := do
  entryPrefix pid
  WorkerCompletion.sourcePrefix pid point

def reschedulePrefix (pid : PeerId) : PrefixM CausalJournal.Event Unit := do
  entryPrefix pid
  let _ ← CausalJournal.transmit pid
  pure ()

theorem EntryPath.worker_prefix (path : EntryPath pid w history ledger u middle)
    (performed : runPrefix (WorkerCompletion.sourcePrefix pid point) u middle = (.ok ((),v),after)) :
    runPrefix (workerPrefix pid point) w history = (.ok ((),v),after) := by
  rw [workerPrefix,runPrefix_bind,path.performed]
  exact performed

theorem EntryPath.reschedule_prefix (path : EntryPath pid w history ledger u middle)
    (performed : runPrefix (CausalJournal.transmit pid) u middle = (.ok (more,v),after)) :
    runPrefix (reschedulePrefix pid) w history = (.ok ((),v),after) := by
  rw [reschedulePrefix,runPrefix_bind,path.performed]
  change runPrefix (CausalJournal.transmit pid >>= fun _ => pure ()) u middle = _
  rw [runPrefix_bind,performed]
  rfl

theorem EntryPath.transmit_failed (path : EntryPath pid w history ledger u middle)
    (activation : Activation) (worker : activation.worker = .txWorker)
    (peer : activation.pid = some pid)
    (performed : runPrefix (CausalJournal.transmit pid) u middle = (.error reason,last)) :
    runPrefix (Driver.iterationObserved CausalJournal.hooks activation) w history = (.error reason,last) := by
  rw [path.iteration_run activation worker peer,tail,runPrefix_bind,performed]

/-- The actual selected callback supplies the matched cut. The literal
activation prefix runs to the identical world and history, retaining the
original failed worker and the same settlement ledger and cleanup debts. -/
theorem selected_cut (activation : Activation)
    (worker : activation.worker = .txWorker) (peer : activation.pid = some pid)
    (entry : EntryPath pid w history ledger u middle)
    (path : SelectionPath ledger [] pid u middle ⟨items,head,true⟩ v after)
    (failed : runPrefix (CausalJournal.transmit pid) u middle = (.error reason,last)) :
    WorkerCompletion.SelectedCut ledger [] pid u middle items head v after reason last ∧
    runPrefix (Driver.iterationObserved CausalJournal.hooks activation) w history = (.error reason,last) ∧
    ∃ context : Context, context.pid = pid ∧ context.locals = [] ∧ context.items = items ∧
      context.initialLedger = ledger ∧
      ∃ point, ∃ saved : Cut context,
        WorkerCompletion.Matched context ledger v after reason last point saved ∧
        runPrefix (workerPrefix pid point) w history = (.ok ((),saved.world),saved.before) ∧
        Staged.Obligations.Step ledger saved.ledger ∧ saved.Valid reason last ∧
        Accounted last saved.ledger saved.debts
          [⟨.selected,pid,saved.phase.active context⟩] saved.world.wg := by
  obtain ⟨original,context,pidEq,localsEq,itemsEq,initial,point,saved,matched,reached,step,valid,accounted⟩ :=
    WorkerCompletion.selected_accounted_cut path failed
  exact ⟨original,entry.transmit_failed activation worker peer failed,
    context,pidEq,localsEq,itemsEq,initial,point,saved,matched,entry.worker_prefix reached,step,valid,accounted⟩

theorem resched_history (w : World) (history : List CausalJournal.Event) :
    (runPrefix (Driver.reschedObserved .txWorker .txNeedResched) w history).2 = history := by
  unfold Driver.reschedObserved
  rw [runPrefix_bind,runPrefix_lift]
  cases (Env.condResched .txWorker).run w <;> rfl

theorem continuation_history (more : Bool) (w : World) (history : List CausalJournal.Event) :
    (runPrefix (continuation more) w history).2 = history := by
  cases more with
  | false => rfl
  | true =>
    simp only [continuation,Bool.not_true,Bool.false_eq_true,↓reduceIte,runPrefix_bind]
    have unchanged := resched_history w history
    cases performed : runPrefix (Driver.reschedObserved .txWorker .txNeedResched) w history with
    | mk outcome after =>
      rw [performed] at unchanged
      cases outcome <;> exact unchanged

/-- This is the actual post-transmit cut, before the native reschedule
continuation. Its Accounted ledger is chosen by the completed worker and
its exact Step, not by the incoming activation carrier. -/
theorem reschedule_cut (path : EntryPath pid w history ledger u middle)
    (transmitted : runPrefix (CausalJournal.transmit pid) u middle = (.ok (true,v),after))
    (returned : Converse.Worker.Returned ledger [] after v)
    (failed : runPrefix (continuation true) v after = (.error reason,last)) :
    ∃ afterLedger, Staged.Obligations.Step ledger afterLedger ∧
      runPrefix (reschedulePrefix pid) w history = (.ok ((),v),after) ∧
      last = after ∧ Accounted last afterLedger [] [] v.wg := by
  obtain ⟨afterLedger,step,accounted⟩ := returned.entry
  have same : last = after := by simpa only [failed] using continuation_history true v after
  exact ⟨afterLedger,step,path.reschedule_prefix transmitted,same,by simpa only [same] using accounted⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.TxActivation
