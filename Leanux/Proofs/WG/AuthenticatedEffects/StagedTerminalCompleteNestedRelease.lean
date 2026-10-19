import Leanux.Proofs.WG.AuthenticatedEffects.StagedTerminalCompleteReleaseSource
import Leanux.Proofs.WG.AuthenticatedEffects.StagedTerminalCompleteReleaseFrames

/-! Whole nested release over one paired Entry/Complete ledger. Access events
retain their real positions, and a failed finish keeps the completed counted
cut rather than assuming that the enclosing caller returned. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedTerminalComplete.Source.Nested
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity RetirementSecurity
open Staged.Obligations AllocatedObligation PeerRelease HandshakeSecurity.StagedDisposal

inductive Frontier (ledger : Ledger) (debts : List CleanupDebt) (locals : List TxLocalBatch)
    (peer : Option PeerId) (w : World) (history : List CausalJournal.Event)
    (stop : Stop) (last : List CausalJournal.Event) : Prop where
  | cutStopped
      (entry : StagedEntry.Inv last ledger debts locals w.wg)
      (complete : Complete last ledger)
      (failed : runWGPrefix (cut peer) w.wg w.ambient history = (.error stop,last))
  | finishStopped (value : Option (PeerId × Peer)) (g : WGWorld) (ambient : Ambient)
      (cutHistory : List CausalJournal.Event) (afterLedger : Ledger)
      (performed : runWGPrefix (cut peer) w.wg w.ambient history = (.ok ((value,g),ambient),cutHistory))
      (step : Staged.Obligations.Step ledger afterLedger) (frame : AllocatedFrame ledger afterLedger)
      (settlement : Successor value w.wg cutHistory.length ledger afterLedger)
      (entry : StagedEntry.Inv (cutHistory ++ [receipt peer value w.wg g w.ambient ambient]) afterLedger debts locals g)
      (complete : Complete (cutHistory ++ [receipt peer value w.wg g w.ambient ambient]) afterLedger)
      (same : last = cutHistory ++ [receipt peer value w.wg g w.ambient ambient])
      (failed : runPrefix (finish value) {w with wg := g,ambient := ambient}
        (cutHistory ++ [receipt peer value w.wg g w.ambient ambient]) = (.error stop,last))

def Returned (ledger : Ledger) (debts : List CleanupDebt) (locals : List TxLocalBatch)
    (peer : Option PeerId) (w : World) (history : List CausalJournal.Event)
    (last : List CausalJournal.Event) (v : World) : Prop :=
  ∃ value g ambient cutHistory afterLedger,
    runWGPrefix (cut peer) w.wg w.ambient history = (.ok ((value,g),ambient),cutHistory) ∧
    last = cutHistory ++ [receipt peer value w.wg g w.ambient ambient] ∧
    Staged.Obligations.Step ledger afterLedger ∧ AllocatedFrame ledger afterLedger ∧
    Successor value w.wg cutHistory.length ledger afterLedger ∧
    StagedEntry.Inv last afterLedger debts locals v.wg ∧ Complete last afterLedger

theorem cut_pair {w : World} (peer : Option PeerId)
    (before : StagedEntry.Inv history ledger debts locals w.wg) (complete : Complete history ledger)
    (performed : runWGPrefix (cut peer) w.wg w.ambient history = (.ok ((value,g),ambient),last)) :
    ∃ afterLedger, Staged.Obligations.Step ledger afterLedger ∧ AllocatedFrame ledger afterLedger ∧
      Successor value w.wg last.length ledger afterLedger ∧
      StagedEntry.Inv (last ++ [receipt peer value w.wg g w.ambient ambient]) afterLedger debts locals g ∧
      Complete (last ++ [receipt peer value w.wg g w.ambient ambient]) afterLedger := by
  obtain ⟨afterLedger,step,frame,settlement,entry⟩ := StagedEntry.Release.cut_entry peer before performed
  obtain ⟨suffix,extended,quiet⟩ := cut_birth_quiet peer w.wg w.ambient history
  rw [performed] at extended
  change last = history ++ suffix at extended
  have entryBefore : StagedEntry.Inv last ledger debts locals w.wg := by
    rw [extended]
    exact before.views suffix quiet rfl rfl rfl rfl rfl rfl
  have historyComplete := cut_complete peer w.wg w.ambient complete
  rw [performed] at historyComplete
  exact ⟨afterLedger,step,frame,settlement,entry,
    release_successor peer ⟨value,w.wg,g,w.ambient,ambient⟩ (cut_valid peer performed)
      entryBefore historyComplete settlement⟩

/-- Actual nested repayment preserves both directions of terminal accounting
on its same fixed successor ledger, including every reached stopped cut. -/
theorem actual_cases {w : World} (peer : Option PeerId)
    (before : StagedEntry.Inv history ledger debts locals w.wg) (complete : Complete history ledger) :
    match (runPrefix (Admission.actualOps.release peer) w history).1 with
    | .error stop => Frontier ledger debts locals peer w history stop
        (runPrefix (Admission.actualOps.release peer) w history).2
    | .ok ((),v) => Returned ledger debts locals peer w history
        (runPrefix (Admission.actualOps.release peer) w history).2 v := by
  rw [actual_run]
  cases performed : runWGPrefix (cut peer) w.wg w.ambient history with
  | mk outcome cutHistory =>
    cases outcome with
    | error stop =>
      have finished := cut_complete peer w.wg w.ambient complete
      rw [performed] at finished
      have entryAt := cut_entry_history peer w.ambient before
      rw [performed] at entryAt
      exact .cutStopped entryAt finished performed
    | ok out =>
      obtain ⟨⟨value,g⟩,ambient⟩ := out
      obtain ⟨afterLedger,step,frame,settlement,entry,finished⟩ := cut_pair peer before complete performed
      simp only []
      cases suffix : runPrefix (finish value) {w with wg := g,ambient := ambient}
        (cutHistory ++ [receipt peer value w.wg g w.ambient ambient]) with
      | mk outcome last =>
        have same := finish_history value {w with wg := g,ambient := ambient}
          (cutHistory ++ [receipt peer value w.wg g w.ambient ambient])
        rw [suffix] at same
        cases outcome with
        | error stop =>
          exact .finishStopped value g ambient cutHistory afterLedger performed
            step frame settlement entry finished same suffix
        | ok out =>
          obtain ⟨ignored,v⟩ := out
          cases ignored
          obtain ⟨hist,final⟩ := StagedEntry.Release.finish_entry value entry suffix
          exact ⟨value,g,ambient,cutHistory,afterLedger,performed,hist,step,frame,settlement,final,
            hist.symm ▸ finished⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedTerminalComplete.Source.Nested
