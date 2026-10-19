import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationCompletionIndexedKeyRelease
import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationCompletionIndexedRelease

/-! Ordinary cleanup performs every native free before repaying references.
The idle debt list is restored at that actual cut. Later key/peer repayment
Stops keep the exact empty-local cut and any real staged-release successor. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.CompletionBatch
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity RetirementSecurity
open TransmitSecurity.Staged.Obligations CompletionCuts HandshakeSecurity.StagedDisposal

private abbrev disposeOps := TxSource.observed CausalJournal.txEvent CausalJournal.txEvent?
  CausalJournal.Event.stagedDisposal

theorem Owned.finished_entry (before : Owned context (.freeing []) history ledger [] w) :
    StagedEntry.Inv history ledger [] context.locals w.wg := by
  refine ⟨before.entry.core,before.entry.justified,before.entry.allocationLinks,before.entry.noSelected,
    before.entry.packets,?_,before.entry.inventory.without_first⟩
  simpa only [TxCoverage,TxOwned,txLocalItems,List.flatMap_cons,List.nil_append,
    Phase.active,TxLocalBatch.items] using before.entry.coverage

inductive DisposeStopped (context : Context) (key : KeypairId) (ledger : Ledger)
    (reason : Stop) (history : List CausalJournal.Event) : Prop where
  | keyStopped (cutWorld : World) (cutHistory : List CausalJournal.Event)
      (owned : Owned context (.freeing []) cutHistory ledger [] cutWorld)
      (failed : runPrefix (disposeOps.access (keypairPutPrefix (some key) false)) cutWorld cutHistory =
        (.error reason,history))
      (frontier : IndexedStopped context ledger [] reason history)
  | peerStopped (cutWorld : World) (cutHistory : List CausalJournal.Event)
      (owned : Owned context (.freeing []) cutHistory ledger [] cutWorld)
      (frontier : IndexedReleaseFrontier context (.freeing []) ledger [] (some context.pid)
        cutWorld cutHistory reason history)

def DisposeReturned (context : Context) (ledger : Ledger) (history : List CausalJournal.Event)
    (value : Bool) (w : World) : Prop :=
  value = true ∧ ∃ after, Staged.Obligations.Step ledger after ∧ AllocatedFrame ledger after ∧
    Owned context (.freeing []) history after [] w ∧
    StagedEntry.Inv history after [] context.locals w.wg ∧
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
theorem indexed_dispose_cases (key : KeypairId)
    (before : Owned context (.freeing context.items) history ledger debts w)
    (localDebts : LocalDebts context context.items debts) :
    ∃ freeWorld freeHistory,
      runPrefix (freeLoop disposeOps context.items) w history = (.ok ((),freeWorld),freeHistory) ∧
      Owned context (.freeing []) freeHistory ledger [] freeWorld ∧
      match (runPrefix (CausalJournal.completionOps.dispose context.pid context.items key) w history).1 with
      | .error reason => DisposeStopped context key ledger reason
          (runPrefix (CausalJournal.completionOps.dispose context.pid context.items key) w history).2
      | .ok (value,v) => DisposeReturned context ledger
          (runPrefix (CausalJournal.completionOps.dispose context.pid context.items key) w history).2 value v := by
  obtain ⟨freeWorld,suffix,freed,atFree⟩ := indexed_freeLoop_total context.items before localDebts
  refine ⟨freeWorld,history ++ suffix,freed,atFree,?_⟩
  change match (runPrefix (TxSource.dispose disposeOps context.pid context.items key) w history).1 with
    | .error reason => DisposeStopped context key ledger reason
        (runPrefix (TxSource.dispose disposeOps context.pid context.items key) w history).2
    | .ok (value,v) => DisposeReturned context ledger
        (runPrefix (TxSource.dispose disposeOps context.pid context.items key) w history).2 value v
  rw [← dispose_factor]
  simp only [dispose,release,runPrefix_bind,freed]
  obtain ⟨_,_,keyChecked⟩ := indexed_keyRelease_checked context key (.freeing []) ledger []
    freeWorld (history ++ suffix) atFree
  cases paid : runPrefix (disposeOps.access (keypairPutPrefix (some key) false))
      freeWorld (history ++ suffix) with
  | mk outcome keyHistory =>
    rw [paid] at keyChecked
    cases outcome with
    | error reason => exact .keyStopped freeWorld (history ++ suffix) atFree paid keyChecked
    | ok result =>
      obtain ⟨ignored,keyWorld⟩ := result
      cases ignored
      dsimp only
      have peerChecked := indexed_release_cases (some context.pid) keyChecked
      change (match (runPrefix (disposeOps.release (some context.pid)) keyWorld keyHistory).1 with
        | .error reason => IndexedReleaseFrontier context (.freeing []) ledger [] (some context.pid)
            keyWorld keyHistory reason (runPrefix (disposeOps.release (some context.pid)) keyWorld keyHistory).2
        | .ok ((),v) => IndexedReleaseReturned context (.freeing []) ledger [] (some context.pid)
            keyWorld keyHistory (runPrefix (disposeOps.release (some context.pid)) keyWorld keyHistory).2 v) at peerChecked
      cases repaid : runPrefix (disposeOps.release (some context.pid)) keyWorld keyHistory with
      | mk outcome peerHistory =>
        rw [repaid] at peerChecked
        cases outcome with
        | error reason => exact .peerStopped keyWorld keyHistory keyChecked peerChecked
        | ok result =>
          obtain ⟨ignored,v⟩ := result
          cases ignored
          obtain ⟨released,g,a,cutHistory,after,cutRun,receiptHistory,step,frame,successor,owned⟩ := peerChecked
          exact ⟨rfl,after,step,frame,owned,owned.finished_entry,
            keyWorld,keyHistory,released,g,a,cutHistory,keyChecked,repaid,cutRun,receiptHistory,successor⟩

end Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.CompletionBatch
