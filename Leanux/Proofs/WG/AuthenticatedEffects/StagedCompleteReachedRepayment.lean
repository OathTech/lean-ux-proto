import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedCleanupCuts
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedReleaseRun

/-! The concrete post-cleanup repayment sequence starts at the exact free
loop output. A key failure retains that entry; a peer failure retains the real
successful key repayment and the selected peer-release source constructor. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity RetirementSecurity
open TransmitSecurity.Staged.Obligations StagedTerminalComplete CompleteCarrier
open AllocatedObligation AllocatedObligation.CompletionBatch
open AllocatedObligation.CompletionBatch.Converse

abbrev keyRepayment (key : KeypairId) := cleanupOps.access (keypairPutPrefix (some key) false)

inductive RepaymentStopped (context : Context) (ledger : Ledger) (key : KeypairId)
    (w : World) (history : List CausalJournal.Event) (reason : Stop)
    (last : List CausalJournal.Event) : Cut context → Prop where
  | keyStopped (owned : Owned context (.freeing []) history ledger [] w)
      (failed : runPrefix (keyRepayment key) w history = (.error reason,last))
      (accounted : Accounted last ledger []
        (⟨.selected,context.pid,[]⟩ :: context.locals) w.wg) :
      RepaymentStopped context ledger key w history reason last
        ⟨ledger,[],.freeing [],w,history,.callback (.keyRelease key)⟩
  | peerStopped (keyWorld : World) (keyHistory : List CausalJournal.Event)
      (paid : runPrefix (keyRepayment key) w history = (.ok ((),keyWorld),keyHistory))
      (owned : Owned context (.freeing []) keyHistory ledger [] keyWorld)
      (complete : Complete keyHistory ledger)
      (projection : ReleaseProjection context (.freeing []) ledger [] (some context.pid)
        keyWorld keyHistory reason last saved) :
      RepaymentStopped context ledger key w history reason last saved

def RepaymentReturned (context : Context) (ledger : Ledger) (key : KeypairId)
    (w : World) (history last : List CausalJournal.Event) (value : Bool) (v : World) : Prop :=
  value = true ∧ ∃ keyWorld keyHistory,
    runPrefix (keyRepayment key) w history = (.ok ((),keyWorld),keyHistory) ∧
    Owned context (.freeing []) keyHistory ledger [] keyWorld ∧ Complete keyHistory ledger ∧
    ReleaseReturned context (.freeing []) ledger [] (some context.pid) keyWorld keyHistory last v

theorem repayment_cases (key : KeypairId)
    (before : Owned context (.freeing []) history ledger [] w) (complete : Complete history ledger) :
    match runPrefix (CompletionBatch.release cleanupOps context.pid key) w history with
    | (.error reason,last) => ∃ saved, RepaymentStopped context ledger key w history reason last saved
    | (.ok (value,v),last) => RepaymentReturned context ledger key w history last value v := by
  have quiet : HistoryFrame ledgerEvent? (keyRepayment key) := focusPrefix_other _ _ _ (fun _ => rfl) _
  obtain ⟨suffix,grown,checked⟩ := indexed_keyRelease_checked context key (.freeing []) ledger [] w history before
  have paired : Complete (runPrefix (keyRepayment key) w history).2 ledger :=
    history_preserved complete (Appends.focus _ _ _) quiet
  unfold CompletionBatch.release
  rw [runPrefix_bind]
  cases paid : runPrefix (keyRepayment key) w history with
  | mk outcome keyHistory =>
    change (runPrefix (keyRepayment key) w history).2 = history ++ suffix at grown
    rw [paid] at grown paired checked
    cases outcome with
    | error reason =>
      have birthFree := ledger_history_birth_free quiet w history suffix
        (by simpa only [paid] using grown)
      have entry := StagedEntry.Queued.Inv.history before.entry suffix birthFree
      refine ⟨_,.keyStopped before paid ?_⟩
      exact ⟨by simpa only [← grown,Phase.active] using entry,paired⟩
    | ok result =>
      obtain ⟨ignored,keyWorld⟩ := result
      cases ignored
      have peerChecked := release_cases (some context.pid) checked paired
      change (match (runPrefix (cleanupOps.release (some context.pid)) keyWorld keyHistory).1 with
        | .error reason => ReleaseStopped context (.freeing []) ledger [] (some context.pid)
          keyWorld keyHistory reason (runPrefix (cleanupOps.release (some context.pid)) keyWorld keyHistory).2
        | .ok ((),v) => ReleaseReturned context (.freeing []) ledger [] (some context.pid)
          keyWorld keyHistory (runPrefix (cleanupOps.release (some context.pid)) keyWorld keyHistory).2 v) at peerChecked
      dsimp only
      rw [runPrefix_bind]
      cases repaid : runPrefix (cleanupOps.release (some context.pid)) keyWorld keyHistory with
      | mk outcome peerHistory =>
        rw [repaid] at peerChecked
        cases outcome with
        | error reason =>
          obtain ⟨saved,projection⟩ := release_project peerChecked
          exact ⟨saved,.peerStopped keyWorld keyHistory paid checked paired projection⟩
        | ok result =>
          obtain ⟨ignored,v⟩ := result
          cases ignored
          exact ⟨rfl,keyWorld,keyHistory,paid,checked,paired,peerChecked⟩

theorem RepaymentStopped.valid
    (stopped : RepaymentStopped context ledger key w history reason last saved) :
    saved.Valid reason last := by
  cases stopped with
  | keyStopped _ failed accounted => exact ⟨failed,accounted⟩
  | peerStopped _ _ _ _ _ projection => exact projection.valid

theorem RepaymentStopped.step
    (stopped : RepaymentStopped context ledger key w history reason last saved) :
    Staged.Obligations.Step ledger saved.ledger := by
  cases stopped with
  | keyStopped => exact .refl _
  | peerStopped _ _ _ _ _ projection => exact projection.step

theorem RepaymentStopped.run
    (stopped : RepaymentStopped context ledger key w history reason last saved) :
    runPrefix (CompletionBatch.release cleanupOps context.pid key) w history = (.error reason,last) := by
  cases stopped with
  | keyStopped _ failed =>
    change runPrefix (keyRepayment key >>= fun _ => _) w history = _
    rw [runPrefix_bind,failed]
  | peerStopped keyWorld keyHistory paid _ _ projection =>
    change runPrefix (keyRepayment key >>= fun _ => _) w history = _
    rw [runPrefix_bind,paid]
    dsimp only
    rw [runPrefix_bind]
    have failed := projection.run
    change runPrefix (cleanupOps.release (some context.pid)) keyWorld keyHistory = _ at failed
    rw [failed]

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached
