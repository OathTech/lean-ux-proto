import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationCompletionCompleteRelease

/-! Ordinary disposal retains completeness on the same native free and
reference-release ledger. The final staged-release successor remains explicit,
and a stopped repayment retains the actual post-cleanup source frontier. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.CompletionBatch.Converse
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity RetirementSecurity
open TransmitSecurity.Staged.Obligations CompletionCuts HandshakeSecurity.StagedDisposal StagedTerminalComplete

private abbrev disposeOps := TxSource.observed CausalJournal.txEvent CausalJournal.txEvent?
  CausalJournal.Event.stagedDisposal

inductive DisposeStopped (context : Context) (key : KeypairId) (ledger : Ledger)
    (reason : Stop) (history : List CausalJournal.Event) : Prop where
  | keyStopped (cutWorld : World) (cutHistory : List CausalJournal.Event)
      (owned : Owned context (.freeing []) cutHistory ledger [] cutWorld)
      (failed : runPrefix (disposeOps.access (keypairPutPrefix (some key) false)) cutWorld cutHistory =
        (.error reason,history))
      (frontier : IndexedStopped context ledger [] reason history)
      (complete : Complete history ledger)
  | peerStopped (cutWorld : World) (cutHistory : List CausalJournal.Event)
      (owned : Owned context (.freeing []) cutHistory ledger [] cutWorld)
      (frontier : ReleaseStopped context (.freeing []) ledger [] (some context.pid)
        cutWorld cutHistory reason history)

def DisposeReturned (context : Context) (ledger : Ledger) (history : List CausalJournal.Event)
    (value : Bool) (w : World) : Prop :=
  value = true ∧ ∃ after, Staged.Obligations.Step ledger after ∧ AllocatedFrame ledger after ∧
    Owned context (.freeing []) history after [] w ∧
    StagedEntry.Inv history after [] context.locals w.wg ∧ Complete history after ∧
    ∃ releaseWorld releaseHistory released g a cutHistory,
      Owned context (.freeing []) releaseHistory ledger [] releaseWorld ∧
      runPrefix (disposeOps.release (some context.pid)) releaseWorld releaseHistory = (.ok ((),w),history) ∧
      runWGPrefix (PeerRelease.cut (some context.pid)) releaseWorld.wg releaseWorld.ambient releaseHistory =
        (.ok ((released,g),a),cutHistory) ∧
      history = cutHistory ++ [PeerRelease.receipt (some context.pid) released
        releaseWorld.wg g releaseWorld.ambient a] ∧
      PeerRelease.Successor released releaseWorld.wg cutHistory.length ledger after

/-- The complete native cleanup suffix supplies all free-success facts.
Every normal result restores the empty incoming debt list and caller locals;
a reference-release Stop retains its actual post-free or post-release cut. -/
theorem dispose_cases (key : KeypairId)
    (before : Owned context (.freeing context.items) history ledger debts w)
    (localDebts : LocalDebts context context.items debts) (complete : Complete history ledger) :
    ∃ freeWorld freeHistory,
      runPrefix (freeLoop disposeOps context.items) w history = (.ok ((),freeWorld),freeHistory) ∧
      Owned context (.freeing []) freeHistory ledger [] freeWorld ∧ Complete freeHistory ledger ∧
      match (runPrefix (CausalJournal.completionOps.dispose context.pid context.items key) w history).1 with
      | .error reason => DisposeStopped context key ledger reason
          (runPrefix (CausalJournal.completionOps.dispose context.pid context.items key) w history).2
      | .ok (value,v) => DisposeReturned context ledger
          (runPrefix (CausalJournal.completionOps.dispose context.pid context.items key) w history).2 value v := by
  obtain ⟨freeWorld,suffix,freed,atFree,freeComplete⟩ := freeLoop_total context.items before localDebts complete
  refine ⟨freeWorld,history ++ suffix,freed,atFree,freeComplete,?_⟩
  change match (runPrefix (TxSource.dispose disposeOps context.pid context.items key) w history).1 with
    | .error reason => DisposeStopped context key ledger reason
        (runPrefix (TxSource.dispose disposeOps context.pid context.items key) w history).2
    | .ok (value,v) => DisposeReturned context ledger
        (runPrefix (TxSource.dispose disposeOps context.pid context.items key) w history).2 value v
  rw [← dispose_factor]
  simp only [dispose,release,runPrefix_bind,freed]
  obtain ⟨_,_,keyChecked⟩ := indexed_keyRelease_checked context key (.freeing []) ledger []
    freeWorld (history ++ suffix) atFree
  have keyComplete : Complete
      (runPrefix (disposeOps.access (keypairPutPrefix (some key) false)) freeWorld (history ++ suffix)).2 ledger :=
    history_preserved freeComplete (Appends.focus _ _ _) (focusPrefix_other _ _ _ (fun _ => rfl) _)
  cases paid : runPrefix (disposeOps.access (keypairPutPrefix (some key) false))
      freeWorld (history ++ suffix) with
  | mk outcome keyHistory =>
    rw [paid] at keyChecked keyComplete
    cases outcome with
    | error reason => exact .keyStopped freeWorld (history ++ suffix) atFree paid keyChecked keyComplete
    | ok result =>
      obtain ⟨ignored,keyWorld⟩ := result
      cases ignored
      dsimp only
      have peerChecked := release_cases (some context.pid) keyChecked keyComplete
      change (match (runPrefix (disposeOps.release (some context.pid)) keyWorld keyHistory).1 with
        | .error reason => ReleaseStopped context (.freeing []) ledger [] (some context.pid)
            keyWorld keyHistory reason (runPrefix (disposeOps.release (some context.pid)) keyWorld keyHistory).2
        | .ok ((),v) => ReleaseReturned context (.freeing []) ledger [] (some context.pid)
            keyWorld keyHistory (runPrefix (disposeOps.release (some context.pid)) keyWorld keyHistory).2 v) at peerChecked
      cases repaid : runPrefix (disposeOps.release (some context.pid)) keyWorld keyHistory with
      | mk outcome peerHistory =>
        rw [repaid] at peerChecked
        cases outcome with
        | error reason => exact .peerStopped keyWorld keyHistory keyChecked peerChecked
        | ok result =>
          obtain ⟨ignored,v⟩ := result
          cases ignored
          obtain ⟨released,g,a,cutHistory,after,cutRun,receiptHistory,step,frame,successor,owned,paired⟩ := peerChecked
          exact ⟨rfl,after,step,frame,owned,owned.finished_entry,paired,
            keyWorld,keyHistory,released,g,a,cutHistory,keyChecked,repaid,cutRun,receiptHistory,successor⟩

end Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.CompletionBatch.Converse
