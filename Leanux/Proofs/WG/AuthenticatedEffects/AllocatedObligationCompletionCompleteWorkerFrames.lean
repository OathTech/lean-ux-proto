import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationCompletionCompleteAccounted

/-! Only the actual queue-selection and readiness leaves are terminal-quiet.
The larger completion event type includes real socket terminals and is not
assumed quiet. These frames include every stopped prefix of these leaves. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.CompletionBatch.Converse
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity RetirementSecurity
open TransmitSecurity.Staged.Obligations StagedTerminalComplete

theorem access_history (action : MixedM α) :
    HistoryFrame ledgerEvent? (FirstTerminal.focused (Completion.access action)) := by
  unfold FirstTerminal.focused Completion.access
  rw [CompletionEffects.focus_composed]
  exact focusPrefix_other _ _ _ (fun _ => rfl) _

theorem step_history (action : WG.M α) : HistoryFrame ledgerEvent? (CausalJournal.completionOps.step action) := by
  intro w h
  change (runPrefix (focusPrefix _ _ (liftPrefix (liftWG action))) w h).2.filterMap ledgerEvent? = _
  change (h ++ ((h.filterMap CausalJournal.completion?).drop (h.filterMap CausalJournal.completion?).length).map FirstTerminal.encode).filterMap ledgerEvent? = _
  simp only [List.drop_length,List.map_nil,List.append_nil]

theorem peek_history (pid : PeerId) : HistoryFrame ledgerEvent? (TxSelection.peek pid) := by
  unfold TxSelection.peek
  apply HistoryFrame.bind (access_history (getPeerMixed pid))
  intro peer
  apply HistoryFrame.bind (step_history peer.txQueue.peek)
  intro pair
  apply HistoryFrame.bind (access_history (modifyPeerKeysPrefix pid fun p => {p with txQueue := pair.2}))
  intro _
  exact HistoryFrame.pure _ _

theorem drop_history (pid : PeerId) (items : List SkbId) :
    HistoryFrame ledgerEvent? (CausalJournal.completionOps.drop pid items) := by
  change HistoryFrame ledgerEvent? (focusPrefix _ _ (focusPrefix _ _ (TxDisposition.drop pid items)))
  rw [CompletionEffects.focus_composed]
  exact focusPrefix_other _ _ _ (fun _ => rfl) _

theorem ready_history (first : Option (List SkbId)) : HistoryFrame ledgerEvent? (TxWorker.ready first) := by
  unfold TxWorker.ready TxDisposition.andObs
  apply HistoryFrame.bind (step_history _)
  intro flag
  cases flag
  · exact HistoryFrame.pure _ _
  · cases first with
    | none => exact step_history _
    | some items =>
      cases items with
      | nil => exact step_history _
      | cons id rest =>
        apply HistoryFrame.bind (access_history (getTxSkbPrefix id))
        intro packet
        exact step_history _

theorem peek_complete (pid : PeerId) (complete : Complete history ledger) (w : World) :
    Complete (runPrefix (TxSelection.peek pid) w history).2 ledger :=
  history_preserved complete (TxSelection.peek_history (fun _ => (none : Option Unit)) (fun _ => rfl) pid).1
    (peek_history pid)

theorem drop_complete (pid : PeerId) (items : List SkbId) (complete : Complete history ledger) (w : World) :
    Complete (runPrefix (CausalJournal.completionOps.drop pid items) w history).2 ledger :=
  history_preserved complete (Appends.focus _ _ _) (drop_history pid items)

theorem ready_complete (first : Option (List SkbId)) (complete : Complete history ledger) (w : World) :
    Complete (runPrefix (TxWorker.ready first) w history).2 ledger :=
  history_preserved complete (TxWorker.ready_history (fun _ => (none : Option Unit)) (fun _ => rfl) first).1
    (ready_history first)

theorem entry_history (before : StagedEntry.Inv history ledger debts locals w)
    (appends : Appends action) (quiet : HistoryFrame ledgerEvent? action) (source : World) :
    StagedEntry.Inv (runPrefix action source history).2 ledger debts locals w := by
  obtain ⟨suffix,grown⟩ := appends source history
  rw [grown]
  exact StagedEntry.Queued.Inv.history before suffix (ledger_history_birth_free quiet source history suffix grown)

end Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.CompletionBatch.Converse
