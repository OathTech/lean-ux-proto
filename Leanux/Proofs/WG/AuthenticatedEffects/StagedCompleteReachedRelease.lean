import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedCuts

/-! Project the actual release constructor to its own accounted entry.
This keeps the completed cut and exact successor ledger when a later finish
fails; it does not replace that successor by an independently chosen account. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity RetirementSecurity
open TransmitSecurity.Staged.Obligations StagedTerminalComplete CompleteCarrier
open AllocatedObligation AllocatedObligation.CompletionBatch
open AllocatedObligation.CompletionBatch.Converse PeerRelease

variable {context : Context} {ledger : Ledger} {debts : List CleanupDebt} {phase : Phase}

inductive ReleaseProjection (context : Context) (phase : Phase) (ledger : Ledger)
    (debts : List CleanupDebt) (peer : Option PeerId) (w : World)
    (history : List CausalJournal.Event) (reason : Stop) (last : List CausalJournal.Event) :
    Cut context → Prop where
  | cutStopped
      (owned : Owned context phase history ledger debts w)
      (failed : runWGPrefix (cut peer) w.wg w.ambient history = (.error reason,last))
      (complete : Complete last ledger) :
      ReleaseProjection context phase ledger debts peer w history reason last
        ⟨ledger,debts,phase,w,history,.releaseCut peer⟩
  | finishStopped (value : Option (PeerId × Peer)) (g : WGWorld) (a : Ambient)
      (cutHistory : List CausalJournal.Event) (after : Ledger)
      (performed : runWGPrefix (cut peer) w.wg w.ambient history = (.ok ((value,g),a),cutHistory))
      (step : Staged.Obligations.Step ledger after) (frame : AllocatedFrame ledger after)
      (settlement : Successor value w.wg cutHistory.length ledger after)
      (owned : Owned context phase (cutHistory ++ [receipt peer value w.wg g w.ambient a]) after debts
        {w with wg := g,ambient := a})
      (complete : Complete last after)
      (failed : runPrefix (PeerRelease.finish value) {w with wg := g,ambient := a}
        (cutHistory ++ [receipt peer value w.wg g w.ambient a]) = (.error reason,last)) :
      ReleaseProjection context phase ledger debts peer w history reason last
        ⟨after,debts,phase,{w with wg := g,ambient := a},
          cutHistory ++ [receipt peer value w.wg g w.ambient a],.releaseFinish value⟩

theorem release_project
    (stopped : ReleaseStopped context phase ledger debts peer w history reason last) :
    ∃ saved, ReleaseProjection context phase ledger debts peer w history reason last saved := by
  cases stopped with
  | cutStopped owned failed complete => exact ⟨_,.cutStopped owned failed complete⟩
  | finishStopped value g a cutHistory after performed step frame settlement owned complete failed =>
    exact ⟨_,.finishStopped value g a cutHistory after performed step frame settlement owned complete failed⟩

theorem ReleaseProjection.original
    (projection : ReleaseProjection context phase ledger debts peer w history reason last saved) :
    ReleaseStopped context phase ledger debts peer w history reason last := by
  cases projection with
  | cutStopped owned failed complete => exact .cutStopped owned failed complete
  | finishStopped value g a cutHistory after performed step frame settlement owned complete failed =>
    exact .finishStopped value g a cutHistory after performed step frame settlement owned complete failed

theorem ReleaseProjection.valid
    (projection : ReleaseProjection context phase ledger debts peer w history reason last saved) :
    saved.Valid reason last := by
  cases projection with
  | cutStopped owned failed complete =>
    have entry := Source.cut_entry_history peer w.ambient owned.entry
    rw [failed] at entry
    refine ⟨?_,entry,complete⟩
    simp only [Action.source,runPrefix_bind,liftWGObserver_run,failed,Except.map]
  | finishStopped value g a cutHistory after performed step frame settlement owned complete failed =>
    have same := PeerRelease.finish_history value {w with wg := g,ambient := a}
      (cutHistory ++ [receipt peer value w.wg g w.ambient a])
    rw [failed] at same
    change last = _ at same
    exact ⟨failed,(by simpa only [same,Cut.locals] using owned.entry),complete⟩

theorem ReleaseProjection.step
    (projection : ReleaseProjection context phase ledger debts peer w history reason last saved) :
    Staged.Obligations.Step ledger saved.ledger := by
  cases projection with
  | cutStopped => exact .refl _
  | finishStopped _ _ _ _ _ _ step => exact step

theorem ReleaseProjection.debts_eq
    (projection : ReleaseProjection context phase ledger debts peer w history reason last saved) :
    saved.debts = debts := by cases projection <;> rfl

theorem ReleaseProjection.phase_eq
    (projection : ReleaseProjection context phase ledger debts peer w history reason last saved) :
    saved.phase = phase := by cases projection <;> rfl

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached
