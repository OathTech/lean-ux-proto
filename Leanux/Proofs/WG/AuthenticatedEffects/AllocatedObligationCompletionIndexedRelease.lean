import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationCompletionIndexedSend
import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntryReleaseSource

/-! Final reference repayment transports the same completion cursor through
any staged-ticket settlement. The actual post-receipt cut, not an unrelated
existential ownership state, is retained when its finish suffix Stops. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.CompletionBatch
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity RetirementSecurity
open TransmitSecurity.Staged.Obligations PeerRelease

/-- The native release cut derives its own packet and ownership frames and
settles only the staged tickets at this precise source receipt. -/
theorem indexed_release_cut (peer : Option PeerId)
    (before : Owned context phase history ledger debts w)
    (performed : runWGPrefix (cut peer) w.wg w.ambient history = (.ok ((value,g),a),last)) :
    ∃ after, Staged.Obligations.Step ledger after ∧ AllocatedFrame ledger after ∧
      Successor value w.wg last.length ledger after ∧
      Owned context phase (last ++ [receipt peer value w.wg g w.ambient a]) after debts
        {w with wg := g,ambient := a} := by
  obtain ⟨after,step,frame,settlement,entry⟩ := StagedEntry.Release.cut_entry peer before.entry performed
  obtain ⟨suffix,extended,quiet⟩ := cut_birth_quiet peer w.wg w.ambient history
  rw [performed] at extended
  change last = history ++ suffix at extended
  have kept := before.append suffix quiet
  rw [← extended] at kept
  refine ⟨after,step,frame,settlement,?_,entry,?_⟩
  · exact (kept.cursor.allocated_frame step frame).append _
  · exact (births_quiet last rfl).trans kept.domain

inductive IndexedReleaseFrontier (context : Context) (phase : Phase) (ledger : Ledger)
    (debts : List CleanupDebt) (peer : Option PeerId) (w : World) (history : List CausalJournal.Event)
    (reason : Stop) (last : List CausalJournal.Event) : Prop where
  | cutStopped
      (owned : Owned context phase history ledger debts w)
      (failed : runWGPrefix (cut peer) w.wg w.ambient history = (.error reason,last))
  | finishStopped (value : Option (PeerId × Peer)) (g : WGWorld) (a : Ambient)
      (cutHistory : List CausalJournal.Event) (after : Ledger)
      (performed : runWGPrefix (cut peer) w.wg w.ambient history = (.ok ((value,g),a),cutHistory))
      (step : Staged.Obligations.Step ledger after) (frame : AllocatedFrame ledger after)
      (settlement : Successor value w.wg cutHistory.length ledger after)
      (owned : Owned context phase (cutHistory ++ [receipt peer value w.wg g w.ambient a]) after debts
        {w with wg := g,ambient := a})
      (failed : runPrefix (PeerRelease.finish value) {w with wg := g,ambient := a}
        (cutHistory ++ [receipt peer value w.wg g w.ambient a]) = (.error reason,last))

def IndexedReleaseReturned (context : Context) (phase : Phase) (ledger : Ledger)
    (debts : List CleanupDebt) (peer : Option PeerId) (w : World) (history last : List CausalJournal.Event)
    (v : World) : Prop :=
  ∃ value g a cutHistory after,
    runWGPrefix (cut peer) w.wg w.ambient history = (.ok ((value,g),a),cutHistory) ∧
    last = cutHistory ++ [receipt peer value w.wg g w.ambient a] ∧
    Staged.Obligations.Step ledger after ∧ AllocatedFrame ledger after ∧
    Successor value w.wg cutHistory.length ledger after ∧
    Owned context phase last after debts v

/-- Complete actual peer repayment preserves allocation terminals and the
same debt list, while an actual final release may settle additional staged
tickets. Stop exposes the precise source cut and its indexed successor. -/
theorem indexed_release_cases (peer : Option PeerId)
    (before : Owned context phase history ledger debts w) :
    match (runPrefix (Admission.actualOps.release peer) w history).1 with
    | .error reason => IndexedReleaseFrontier context phase ledger debts peer w history reason
        (runPrefix (Admission.actualOps.release peer) w history).2
    | .ok ((),v) => IndexedReleaseReturned context phase ledger debts peer w history
        (runPrefix (Admission.actualOps.release peer) w history).2 v := by
  rw [actual_run]
  cases performed : runWGPrefix (cut peer) w.wg w.ambient history with
  | mk outcome cutHistory =>
    cases outcome with
    | error reason => exact .cutStopped before performed
    | ok result =>
      obtain ⟨⟨value,g⟩,a⟩ := result
      obtain ⟨after,step,frame,settlement,atCut⟩ := indexed_release_cut peer before performed
      dsimp only
      cases suffix : runPrefix (PeerRelease.finish value) {w with wg := g,ambient := a}
          (cutHistory ++ [receipt peer value w.wg g w.ambient a]) with
      | mk outcome last =>
        cases outcome with
        | error reason => exact .finishStopped value g a cutHistory after performed step frame settlement atCut suffix
        | ok result =>
          obtain ⟨ignored,v⟩ := result
          cases ignored
          obtain ⟨same,entry⟩ := StagedEntry.Release.finish_entry value atCut.entry suffix
          exact ⟨value,g,a,cutHistory,after,performed,same,step,frame,settlement,
            (by simpa only [same] using atCut.cursor),entry,(by simpa only [same] using atCut.domain)⟩

end Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.CompletionBatch
