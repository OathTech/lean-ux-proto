import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationCreateEntryFrames

/-! Result-aware createData admission. The only queued ownership transfer is
the original queue write. On a stopped publication this theorem retains its
actual queued entry and failed callback, not an invented final World. Finer
publication-internal stopped cuts are exposed separately by its source factor. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.CreateEntry
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity RetirementSecurity
open HandshakeSecurity.StagedDisposal Staged.Obligations Admission
set_option pp.structureInstances false
set_option maxHeartbeats 600000

inductive FrontStop (ledger : Ledger) (debts : List CleanupDebt)
    (locals : List TxLocalBatch) (pid : PeerId) (items : List SkbId)
    (w : World) (history : List CausalJournal.Event) (stop : Stop)
    (last : List CausalJournal.Event) : Prop where
  | readStopped
      (owned : StagedEntry.Inv history ledger debts (⟨.unpublished,pid,items⟩ :: locals) w.wg)
      (failed : runPrefix (actualOps.access (getPeerMixed pid)) w history = (.error stop,last))
  | enqueueStopped (p : Peer) (u v : World) (readHistory : List CausalJournal.Event)
      (read : runPrefix (actualOps.access (getPeerMixed pid)) w history = (.ok (p,u),readHistory))
      (guard : runPrefix (actualOps.step (branch .createDataDead p.isDead)) u readHistory =
        (.ok (false,v),readHistory))
      (frontier : StagedEntry.Queue.EnqueueFrontier ledger debts locals pid items v readHistory stop last)
  | publicationStopped (p : Peer) (u v q r : World) (readHistory queuedHistory : List CausalJournal.Event)
      (read : runPrefix (actualOps.access (getPeerMixed pid)) w history = (.ok (p,u),readHistory))
      (guard : runPrefix (actualOps.step (branch .createDataDead p.isDead)) u readHistory =
        (.ok (false,v),readHistory))
      (enqueued : runPrefix (actualOps.enqueue pid items) v readHistory = (.ok (-WG.EPIPE,q),queuedHistory))
      (pipe : runPrefix (actualOps.step (branch .createDataEpipe true)) q queuedHistory =
        (.ok (true,r),queuedHistory))
      (owned : StagedEntry.Inv queuedHistory ledger debts locals r.wg)
      (failed : runPrefix (TxSource.publish actualOps items .dead) r queuedHistory = (.error stop,last))

def FrontReturned (ledger : Ledger) (debts : List CleanupDebt) (locals : List TxLocalBatch)
    (pid : PeerId) (items : List SkbId) (ret : Int) (history : List CausalJournal.Event) (w : World) : Prop :=
  ((ret = -EINVAL ∨ ret = -WG.ENOSPC) ∧ StagedEntry.Inv history ledger debts (⟨.unpublished,pid,items⟩ :: locals) w.wg) ∨
    ((ret = 0 ∨ ret = -WG.EPIPE) ∧ StagedEntry.Inv history ledger debts locals w.wg)

/-- Actual dead/full guards and EPIPE publication retain the same canonical
ledger. Every stopped result identifies a real source callback and its actual
unpublished or queued ownership cut; normal results retain the returned phase. -/
theorem front_cases (pid : PeerId) (items : List SkbId)
    (owned : StagedEntry.Inv history ledger debts (⟨.unpublished,pid,items⟩ :: locals) w.wg) :
    match (runPrefix (actual pid items) w history).1 with
    | .error stop => FrontStop ledger debts locals pid items w history stop (runPrefix (actual pid items) w history).2
    | .ok (ret,v) => FrontReturned ledger debts locals pid items ret (runPrefix (actual pid items) w history).2 v := by
  unfold actual front
  simp only [runPrefix_bind]
  cases read : runPrefix (actualOps.access (getPeerMixed pid)) w history with
  | mk outcome readHistory =>
    cases outcome with
    | error stop => exact .readStopped owned read
    | ok out =>
      obtain ⟨p,u⟩ := out
      have readOwn := read_peer_entry pid owned read
      obtain ⟨v,guard,guardOwn⟩ := guard_entry .createDataDead p.isDead readOwn
      simp only []
      rw [guard]
      cases dead : p.isDead with
      | true =>
        simp only [ite_true,runPrefix_pure]
        exact Or.inl ⟨Or.inl rfl,guardOwn⟩
      | false =>
        simp only [Bool.false_eq_true,ite_false,runPrefix_bind]
        have queued := StagedEntry.Queue.enqueue_cases pid items guardOwn
        cases enqueue : runPrefix (actualOps.enqueue pid items) v readHistory with
        | mk result queuedHistory =>
          rw [enqueue] at queued
          cases result with
          | error stop => exact .enqueueStopped p u v readHistory read (by simpa [dead] using guard) queued
          | ok out =>
            obtain ⟨ret,q⟩ := out
            simp only []
            rcases queued with ⟨code,unpublished⟩ | ⟨code,published⟩
            · subst ret
              obtain ⟨r,pipe,final⟩ := guard_entry .createDataEpipe false unpublished
              rw [show (-WG.ENOSPC == -WG.EPIPE) = false from rfl,pipe]
              simp only [Bool.false_eq_true,ite_false,runPrefix_pure]
              exact Or.inl ⟨Or.inr rfl,final⟩
            · rcases code with code | code
              · subst ret
                obtain ⟨r,pipe,final⟩ := guard_entry .createDataEpipe false published
                rw [show ((0 : Int) == -WG.EPIPE) = false from rfl,pipe]
                simp only [Bool.false_eq_true,ite_false,runPrefix_pure]
                exact Or.inr ⟨Or.inl rfl,final⟩
              · subst ret
                obtain ⟨r,pipe,atPublish⟩ := guard_entry .createDataEpipe true published
                rw [show (-WG.EPIPE == -WG.EPIPE) = true from rfl,pipe]
                simp only [ite_true,runPrefix_bind]
                cases publication : runPrefix (TxSource.publish actualOps items .dead) r queuedHistory with
                | mk result last =>
                  cases result with
                  | error stop =>
                    exact .publicationStopped p u v q r readHistory queuedHistory read
                      (by simpa [dead] using guard) enqueue pipe atPublish publication
                  | ok out =>
                    obtain ⟨ignored,s⟩ := out
                    cases ignored
                    simp only [runPrefix_pure]
                    exact Or.inr ⟨Or.inr rfl,publication_entry items .dead atPublish publication⟩

end Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.CreateEntry
