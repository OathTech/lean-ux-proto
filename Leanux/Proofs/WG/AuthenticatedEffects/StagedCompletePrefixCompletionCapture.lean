import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompletePrefixCompletionContracts

/-! The packet receipt is the actual current native capture. Prefix extension
preserves the same explicit completion ledger and the original stopped result. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompletePrefix.Completion
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity
open AllocatedObligation CompletionBatch Staged.Obligations StagedTerminalComplete

variable {Safe : List CausalJournal.Event → Prop}

theorem access_quiet (action : MixedM α) :
    HistoryFrame ledgerEvent? (FirstTerminal.focused (Completion.access action)) := by
  intro w h
  change (h ++ List.map FirstTerminal.encode _).filterMap ledgerEvent? = _
  rw [List.filterMap_append,List.filterMap_map]
  have inner : HistoryFrame (fun e => ledgerEvent? (FirstTerminal.encode e)) (Completion.access action) :=
    focusPrefix_other _ _ _ (fun _ => rfl) _
  have appends : Appends (Completion.access action) := Appends.focus _ _ _
  obtain ⟨events,grown⟩ := appends w (h.filterMap CausalJournal.completion?)
  have empty : events.filterMap (fun e => ledgerEvent? (FirstTerminal.encode e)) = [] := by
    have same := inner w (h.filterMap CausalJournal.completion?)
    rw [grown,List.filterMap_append] at same
    exact List.append_cancel_left (by simpa only [List.append_nil] using same)
  simp only [grown,List.drop_left]
  change h.filterMap ledgerEvent? ++ events.filterMap (fun e => ledgerEvent? (FirstTerminal.encode e)) = _
  rw [empty,List.append_nil]

theorem packet (context : Context) (skb : SkbId) (remaining : List SkbId)
    (ledger : Ledger) (debts : List CleanupDebt) (accountSafe : AccountSafe Safe) :
    Checked (fun h w => Owned context (.sending (skb :: remaining)) h ledger debts w ∧ Complete h ledger)
      Safe (fun reason h => IndexedStopped context ledger debts reason h ∧ Complete h ledger)
      (captureObserved (CausalJournal.completionOps.packet skb))
      (fun receipt h w => Owned context (.sending (skb :: remaining)) h ledger debts w ∧
        PacketAt skb receipt w ∧ Complete h ledger) := by
  have appends : Appends (captureObserved (CausalJournal.completionOps.packet skb)) :=
    Appends.captureObserved (Appends.focus _ _ _)
  have quiet : HistoryFrame ledgerEvent? (captureObserved (CausalJournal.completionOps.packet skb)) := by
    intro w h
    change (runPrefix (FirstTerminal.focused (Completion.access (getTxSkbPrefix skb))) w h).2.filterMap _ = _
    exact access_quiet _ w h
  apply Checked.of_cuts
  · intro w h before
    obtain ⟨suffix,grown,result⟩ := indexed_packet_checked context skb remaining ledger debts w h before.1
    have complete := Converse.history_preserved before.2 appends quiet (w := w)
    refine ⟨suffix,grown,?_⟩
    cases run : (runPrefix (captureObserved (CausalJournal.completionOps.packet skb)) w h).1 with
    | error reason => exact ⟨by simpa only [run] using result,complete⟩
    | ok out =>
      have returned := (show Owned context (.sending (skb :: remaining)) _ ledger debts out.2 ∧
        PacketAt skb out.1 out.2 from by simpa only [run] using result)
      exact ⟨returned.1,returned.2,complete⟩
  · intro w h before
    exact quiet_output accountSafe before.1 before.2 appends quiet

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompletePrefix.Completion
