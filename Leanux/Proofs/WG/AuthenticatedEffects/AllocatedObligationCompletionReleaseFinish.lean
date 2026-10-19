import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationCompletionReleaseEntry

/-! The final-reference receipt precedes the original timer check and dispatch
retirement. A failure in that suffix retains the post-disposal world and the
same indexed ledger, rather than reverting to the pre-release ownership cut. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.CompletionBatch
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity TransmitSecurity.Staged.Origins TransmitSecurity.Staged.Obligations
open RetirementSecurity HandshakeSecurity.StagedDisposal CompletionCuts

theorem finish_entry_view (pid : PeerId) (peer : Peer) :
    SameView StagedEntry.view (releaseFinish pid peer) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a result v b run
  cases found : PeerTimer.all.find? (fun timer => peer.timerPending timer || (peer.wheel timer).isSome) with
  | some timer =>
    simp [releaseFinish,found,invariant,AmbientM.invariant] at run
    cases run
  | none =>
    simp [releaseFinish,found,retirePeerUnits,modifyAmbient,StateT.run_bind,
      StateT.run_monadLift,
      CounterWindow.except_pure] at run
    rcases run with ⟨rfl,rfl⟩
    rfl

def releaseFinishObserved (pid : PeerId) (peer : Peer) : PrefixM CausalJournal.Event Unit :=
  liftPrefix (liftWG (releaseFinish pid peer))

structure AtRelease (context : Context) (phase : Phase) (ledger : Ledger)
    (debts : List CleanupDebt) (pid : PeerId) (peer : Peer)
    (history : List CausalJournal.Event) (w : World) : Prop where
  owned : Owned context phase history ledger debts w
  receipt : ∃ (before : List CausalJournal.Event) (owner : Option PeerId) (r : WGRunWitness (Option (PeerId × Peer))),
    history = before ++ [.stagedDisposal (.release owner r)] ∧
    r.Valid (releaseCut owner) ∧ r.value = some (pid,peer) ∧
    w.wg = r.after ∧ w.ambient = r.ambientAfter

structure FinishFrontier (context : Context) (phase : Phase) (ledger : Ledger)
    (debts : List CleanupDebt) (pid : PeerId) (peer : Peer)
    (reason : Stop) (history : List CausalJournal.Event) where
  world : World
  atRelease : AtRelease context phase ledger debts pid peer history world
  failed : runPrefix (releaseFinishObserved pid peer) world history = (.error reason,history)

/-- The real post-release suffix either preserves the complete indexed entry
or stops with that same counted release already present. Neither result loses
the caller-local batch or any first-terminal cleanup debt. -/
theorem releaseFinish_checked (context : Context) (phase : Phase) (ledger : Ledger)
    (debts : List CleanupDebt) (pid : PeerId) (peer : Peer) :
    Ensures (AtRelease context phase ledger debts pid peer)
      (fun reason history => Nonempty (FinishFrontier context phase ledger debts pid peer reason history))
      (releaseFinishObserved pid peer) (fun _ h w => Owned context phase h ledger debts w) := by
  intro w history before
  simp only [releaseFinishObserved,runPrefix_lift]
  refine ⟨[],by simp,?_⟩
  cases run : (liftWG (releaseFinish pid peer)).run w with
  | error reason =>
    refine ⟨⟨w,before,?_⟩⟩
    exact congrArg (fun result => (result,history)) run
  | ok result =>
    obtain ⟨value,v⟩ := result
    have lifted : SameView (fun world : World => StagedEntry.view world.wg)
        (liftWG (releaseFinish pid peer)) :=
      sameView_liftWG _ _ _ (finish_entry_view pid peer) (fun _ _ _ same => same)
    have equal := (ProjectedAction.iff_run _ _ _).mp lifted w value v run
    exact ⟨before.owned.cursor,before.owned.entry.same_view equal,before.owned.domain⟩

end Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.CompletionBatch
