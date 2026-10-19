import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationCompletionCompleteTxWorker

/-! Every stopped worker path retains both its actual source frontier and
an accounted saved cut. Intermediate cleanup debts and selected locals are
allowed at Stop; normal paths still restore empty debts and caller locals. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.CompletionBatch.Converse.Worker
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity RetirementSecurity
open Staged.Obligations StagedEntry.CompleteCarrier StagedTerminalComplete

private theorem quiet_accounted {w : World} {action : PrefixM CausalJournal.Event α}
    (before : Accounted history ledger debts locals w.wg)
    (appends : Appends action) (quiet : HistoryFrame ledgerEvent? action)
    (failed : runPrefix action w history = (.error reason,last)) : Accounted last ledger debts locals w.wg := by
  have entry := entry_history before.entry appends quiet w
  have complete := history_preserved before.complete appends quiet (w := w)
  rw [failed] at entry complete
  exact ⟨entry,complete⟩

def AccountedCut (ledger : Ledger) (history : List CausalJournal.Event) : Prop :=
  ∃ after debts locals cut,
    Staged.Obligations.Step ledger after ∧ Accounted history after debts locals cut

theorem DispatchStop.accounted
    (frontier : DispatchStop ledger locals pid items head w history reason last) : AccountedCut ledger last := by
  cases frontier with
  | crypted _ _ _ _ _ stopped => exact (worker_stopped_accounted stopped).2
  | dead _ _ _ _ _ stopped =>
    obtain ⟨after,cut,step,accounted⟩ := stopped.accounted
    exact ⟨after,[],locals,cut,step,accounted⟩

theorem AfterReadStop.accounted
    (frontier : AfterReadStop ledger locals pid items head w history reason last) : AccountedCut ledger last := by
  cases frontier with
  | drop before _ failed =>
    exact ⟨ledger,[],locals,w.wg,.refl _,quiet_accounted before (Appends.focus _ _ _) (drop_history pid items) failed⟩
  | dispatch _ _ _ _ _ stopped => exact stopped.accounted

theorem BodyStop.accounted
    (frontier : BodyStop ledger locals pid first w history reason last) : AccountedCut ledger last := by
  cases frontier with
  | ready before failed =>
    exact ⟨ledger,[],locals,w.wg,.refl _,quiet_accounted before
      (TxWorker.ready_history (fun _ => (none : Option Unit)) (fun _ => rfl) first).1
      (ready_history first) failed⟩
  | packet u _ _ id _ _ _ before failed =>
    exact ⟨ledger,[],locals,u.wg,.refl _,quiet_accounted before
      (Appends.focus _ _ _) (access_history (getTxSkbPrefix id)) failed⟩
  | afterRead _ _ _ _ _ _ _ _ _ _ _ _ stopped => exact stopped.accounted

theorem TransmitStop.accounted
    (frontier : TransmitStop ledger locals pid w history reason last) : AccountedCut ledger last := by
  cases frontier with
  | peek before failed =>
    exact ⟨ledger,[],locals,w.wg,.refl _,quiet_accounted before
      (TxSelection.peek_history (fun _ => (none : Option Unit)) (fun _ => rfl) pid).1
      (peek_history pid) failed⟩
  | body _ _ _ _ _ _ stopped => exact stopped.accounted

/-- The saved-cut projection accompanies the original recursive frontier;
none of its actual failed runs or terminal settlement witnesses is replaced. -/
theorem transmit_checked (pid : PeerId) (before : Accounted history ledger [] locals w.wg) :
    match (runPrefix (CausalJournal.transmit pid) w history).1 with
    | .error reason => TransmitStop ledger locals pid w history reason
        (runPrefix (CausalJournal.transmit pid) w history).2 ∧
        AccountedCut ledger (runPrefix (CausalJournal.transmit pid) w history).2
    | .ok (_,v) => Returned ledger locals (runPrefix (CausalJournal.transmit pid) w history).2 v := by
  have checked := transmit_cases pid before
  cases result : runPrefix (CausalJournal.transmit pid) w history with
  | mk outcome last =>
    rw [result] at checked
    cases outcome with
    | error reason => exact ⟨checked,checked.accounted⟩
    | ok out => exact checked

end Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.CompletionBatch.Converse.Worker
