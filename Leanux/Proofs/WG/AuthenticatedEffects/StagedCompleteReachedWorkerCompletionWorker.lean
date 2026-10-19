import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedWorkerCompletionCuts

/-! The actual full worker chooses the selected completion entry. Crypted
failures now have matched fixed worker prefixes; early selection and DEAD
failures retain their original source paths for their separate interval proofs. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.WorkerCompletion
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity RetirementSecurity
open TransmitSecurity.Staged.Obligations StagedTerminalComplete CompleteCarrier
open AllocatedObligation CompletionBatch

def SelectedCut (ledger : Ledger) (locals : List TxLocalBatch) (pid : PeerId)
    (w : World) (history : List CausalJournal.Event) (items : List SkbId) (head : DataPacket)
    (u : World) (middle : List CausalJournal.Event) (reason : Stop) (last : List CausalJournal.Event) : Prop :=
  ∃ context : Context, context.pid = pid ∧ context.locals = locals ∧ context.items = items ∧
    context.initialLedger = ledger ∧ context.births = births middle ∧
    Owned context (.sending context.items) middle ledger [] u ∧ Complete middle ledger ∧
    runPrefix (TxWorker.crypted pid items head) u middle = (.error reason,last) ∧
    runPrefix (CausalJournal.transmit pid) w history = (.error reason,last) ∧
    ∃ point, ∃ saved : Cut context,
      Matched context ledger u middle reason last point saved ∧
      runPrefix (sourcePrefix pid point) w history = (.ok ((),saved.world),saved.before) ∧
      saved.Valid reason last

theorem selected_failure
    (path : SelectionPath ledger locals pid w history ⟨items,head,true⟩ u middle)
    (failed : runPrefix (CausalJournal.transmit pid) w history = (.error reason,last)) :
    SelectedCut ledger locals pid w history items head u middle reason last := by
  have ⟨account,pending⟩ := path.accounted_entry
  have interval := worker_interval pid items head account.entry account.complete pending
  have callback : runPrefix (TxWorker.crypted pid items head) u middle = (.error reason,last) := by
    rw [path.callback_run] at failed
    exact failed
  rw [callback] at interval
  exact selected_cut path interval

inductive WorkerStop (ledger : Ledger) (locals : List TxLocalBatch) (pid : PeerId)
    (w : World) (history : List CausalJournal.Event) (reason : Stop) (last : List CausalJournal.Event) : Prop where
  | selecting (performed : runPrefix (workerSelection pid) w history = (.error reason,last))
  | dead (items : List SkbId) (head : DataPacket) (u : World) (middle : List CausalJournal.Event)
      (path : SelectionPath ledger locals pid w history ⟨items,head,false⟩ u middle)
      (performed : runPrefix (selectedCallback pid (some ⟨items,head,false⟩)) u middle = (.error reason,last))
      (frontier : Converse.Dead.Stopped ledger [] locals pid items head u middle reason last)
  | crypted (items : List SkbId) (head : DataPacket) (u : World) (middle : List CausalJournal.Event)
      (path : SelectionPath ledger locals pid w history ⟨items,head,true⟩ u middle)
      (result : SelectedCut ledger locals pid w history items head u middle reason last)

theorem WorkerStop.source_failed
    (stopped : WorkerStop ledger locals pid w history reason last) :
    runPrefix (CausalJournal.transmit pid) w history = (.error reason,last) := by
  cases stopped with
  | selecting performed => rw [worker_selection_factor,runPrefix_bind,performed]
  | dead _ _ _ _ path performed => rw [path.callback_run,performed]
  | crypted _ _ _ _ _ result =>
    obtain ⟨_,_,_,_,_,_,_,_,_,native,_⟩ := result
    exact native

/-- The old full recursive frontier is retained. In the crypted arm the
new cut comes from the actual selected callback, never from that frontier's
unrelated existential saved world. -/
theorem worker_failed (pid : PeerId)
    (before : Accounted history ledger [] locals w.wg)
    (failed : runPrefix (CausalJournal.transmit pid) w history = (.error reason,last)) :
    Converse.Worker.TransmitStop ledger locals pid w history reason last ∧
      WorkerStop ledger locals pid w history reason last := by
  obtain ⟨original,selected⟩ := transmit_stopped_cut pid before failed
  refine ⟨original,?_⟩
  cases selected with
  | selecting performed => exact .selecting performed
  | selected picked u middle path callback =>
    cases callback with
    | crypted items head performed interval =>
      exact .crypted items head u middle path (selected_cut path interval)
    | dead items head performed frontier =>
      exact .dead items head u middle path performed frontier

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.WorkerCompletion
