import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationCompletionCompleteSequence
import Leanux.Proofs.WG.AuthenticatedEffects.StagedTerminalCompleteReleaseSource
import Leanux.Proofs.WG.AuthenticatedEffects.StagedTerminalCompleteReleaseFrames

/-! The actual final repayment carries terminal completeness on precisely
its source-derived successor ledger. A stopped release finish retains the
recorded staged disposal and the same selected completion ownership. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.CompletionBatch.Converse
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity RetirementSecurity
open TransmitSecurity.Staged.Obligations PeerRelease StagedTerminalComplete

theorem release_cut_complete (peer : Option PeerId)
    (before : Owned context phase history ledger debts w) (complete : Complete history ledger)
    (performed : runWGPrefix (cut peer) w.wg w.ambient history = (.ok ((value,g),a),last))
    (successor : Successor value w.wg last.length ledger after) :
    Complete (last ++ [receipt peer value w.wg g w.ambient a]) after := by
  have entryAt := StagedTerminalComplete.Source.cut_entry_history peer w.ambient before.entry
  have completeAt := StagedTerminalComplete.Source.cut_complete peer w.wg w.ambient complete
  rw [performed] at entryAt completeAt
  exact StagedTerminalComplete.Source.release_successor peer ⟨value,w.wg,g,w.ambient,a⟩
    (cut_valid peer performed) entryAt completeAt successor

inductive ReleaseStopped (context : Context) (phase : Phase) (ledger : Ledger)
    (debts : List CleanupDebt) (peer : Option PeerId) (w : World) (history : List CausalJournal.Event)
    (reason : Stop) (last : List CausalJournal.Event) : Prop where
  | cutStopped
      (owned : Owned context phase history ledger debts w)
      (failed : runWGPrefix (cut peer) w.wg w.ambient history = (.error reason,last))
      (complete : Complete last ledger)
  | finishStopped (value : Option (PeerId × Peer)) (g : WGWorld) (a : Ambient)
      (cutHistory : List CausalJournal.Event) (after : Ledger)
      (performed : runWGPrefix (cut peer) w.wg w.ambient history = (.ok ((value,g),a),cutHistory))
      (step : Staged.Obligations.Step ledger after) (frame : AllocatedFrame ledger after)
      (settlement : Successor value w.wg cutHistory.length ledger after)
      (owned : Owned context phase (cutHistory ++ [receipt peer value w.wg g w.ambient a]) after debts
        {w with wg := g,ambient := a})
      (complete : Complete last after)
      (failed : runPrefix (PeerRelease.finish value) {w with wg := g,ambient := a}
        (cutHistory ++ [receipt peer value w.wg g w.ambient a]) = (.error reason,last))

def ReleaseReturned (context : Context) (phase : Phase) (ledger : Ledger)
    (debts : List CleanupDebt) (peer : Option PeerId) (w : World) (history last : List CausalJournal.Event)
    (v : World) : Prop :=
  ∃ value g a cutHistory after,
    runWGPrefix (cut peer) w.wg w.ambient history = (.ok ((value,g),a),cutHistory) ∧
    last = cutHistory ++ [receipt peer value w.wg g w.ambient a] ∧
    Staged.Obligations.Step ledger after ∧ AllocatedFrame ledger after ∧
    Successor value w.wg cutHistory.length ledger after ∧
    Owned context phase last after debts v ∧ Complete last after

/-- Complete actual peer repayment preserves allocation terminals and the
same debt list, while an actual final release may settle additional staged
tickets. Stop exposes the precise source cut and its indexed successor. -/
theorem release_cases (peer : Option PeerId)
    (before : Owned context phase history ledger debts w) (complete : Complete history ledger) :
    match (runPrefix (Admission.actualOps.release peer) w history).1 with
    | .error reason => ReleaseStopped context phase ledger debts peer w history reason
        (runPrefix (Admission.actualOps.release peer) w history).2
    | .ok ((),v) => ReleaseReturned context phase ledger debts peer w history
        (runPrefix (Admission.actualOps.release peer) w history).2 v := by
  rw [actual_run]
  cases performed : runWGPrefix (cut peer) w.wg w.ambient history with
  | mk outcome cutHistory =>
    cases outcome with
    | error reason =>
      have paired := StagedTerminalComplete.Source.cut_complete peer w.wg w.ambient complete
      rw [performed] at paired
      exact .cutStopped before performed paired
    | ok result =>
      obtain ⟨⟨value,g⟩,a⟩ := result
      obtain ⟨after,step,frame,settlement,atCut⟩ := indexed_release_cut peer before performed
      have paired := release_cut_complete peer before complete performed settlement
      dsimp only
      cases suffix : runPrefix (PeerRelease.finish value) {w with wg := g,ambient := a}
          (cutHistory ++ [receipt peer value w.wg g w.ambient a]) with
      | mk outcome last =>
        have same := PeerRelease.finish_history value {w with wg := g,ambient := a}
          (cutHistory ++ [receipt peer value w.wg g w.ambient a])
        rw [suffix] at same
        change last = cutHistory ++ [receipt peer value w.wg g w.ambient a] at same
        have completeLast : Complete last after := by rw [same]; exact paired
        cases outcome with
        | error reason => exact .finishStopped value g a cutHistory after performed step frame settlement atCut completeLast suffix
        | ok result =>
          obtain ⟨ignored,v⟩ := result
          cases ignored
          obtain ⟨same,entry⟩ := StagedEntry.Release.finish_entry value atCut.entry suffix
          exact ⟨value,g,a,cutHistory,after,performed,same,step,frame,settlement,
            ⟨(by simpa only [same] using atCut.cursor),entry,(by simpa only [same] using atCut.domain)⟩,completeLast⟩

end Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.CompletionBatch.Converse
