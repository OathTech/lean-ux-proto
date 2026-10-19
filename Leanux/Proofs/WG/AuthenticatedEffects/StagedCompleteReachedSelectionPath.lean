import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedSelectionSource

/-! The successful native selection interval retains the original worker
entry, the original queue-dequeue run, and ownership on both sides of that
run. The selected callback state is chosen by this fixed source path. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity RetirementSecurity
open TransmitSecurity.Staged.Obligations StagedTerminalComplete CompleteCarrier
open AllocatedObligation AllocatedObligation.CompletionBatch

inductive SelectionPath (ledger : Ledger) (locals : List TxLocalBatch) (pid : PeerId)
    (w : World) (history : List CausalJournal.Event) (picked : Selected)
    (v : World) (last : List CausalJournal.Event) : Prop where
  | intro (peekWorld readyWorld readWorld dropWorld : World)
      (peekHistory readyHistory readHistory : List CausalJournal.Event) (id : SkbId)
      (initial : Accounted history ledger [] locals w.wg)
      (peeked : runPrefix (TxSelection.peek pid) w history = (.ok (some picked.items,peekWorld),peekHistory))
      (readied : runPrefix (TxWorker.ready (some picked.items)) peekWorld peekHistory =
        (.ok (true,readyWorld),readyHistory))
      (nonempty : picked.items.head? = some id)
      (read : runPrefix (CausalJournal.completionOps.packet id) readyWorld readyHistory =
        (.ok (picked.head,readWorld),readHistory))
      (beforeDrop : Accounted readHistory ledger [] locals readWorld.wg)
      (removed : runPrefix (CausalJournal.completionOps.drop pid picked.items) readWorld readHistory =
        (.ok ((),dropWorld),last))
      (afterDrop : Accounted last ledger [] (⟨.selected,pid,picked.items⟩ :: locals) dropWorld.wg)
      (guarded : runPrefix (CausalJournal.completionOps.step
        (branch .txCrypted (picked.head.state == .crypted))) dropWorld last = (.ok (picked.crypted,v),last))
      (afterGuard : Accounted last ledger [] (⟨.selected,pid,picked.items⟩ :: locals) v.wg)
      (pending : CreateDisposal.PendingBatch last ledger picked.items)

/-- The exact native selection prefix reaches the saved callback entry.
The ownership transfer is the original queue removal recorded in `path`. -/
theorem SelectionPath.run (path : SelectionPath ledger locals pid w history picked v last) :
    runPrefix (workerSelection pid) w history = (.ok (some picked,v),last) := by
  cases path with
  | intro pw rw sw dw ph rh sh id initial peeked readied nonempty read beforeDrop removed afterDrop guarded afterGuard pending =>
    unfold workerSelection bodySelection
    rw [runPrefix_bind,peeked]
    dsimp only
    rw [runPrefix_bind,readied]
    simp only [Bool.not_true,Bool.false_eq_true,↓reduceIte,nonempty]
    rw [runPrefix_bind,read]
    dsimp only
    unfold afterReadSelection
    rw [runPrefix_bind,runPrefix_bind,removed]
    dsimp only
    rw [runPrefix_bind,guarded]
    simp only [runPrefix_pure]

theorem SelectionPath.callback_run
    (path : SelectionPath ledger locals pid w history picked v last) :
    runPrefix (CausalJournal.transmit pid) w history =
      runPrefix (selectedCallback pid (some picked)) v last := by
  rw [worker_selection_factor,runPrefix_bind,path.run]

theorem SelectionPath.accounted_entry
    (path : SelectionPath ledger locals pid w history picked v last) :
    Accounted last ledger [] (⟨.selected,pid,picked.items⟩ :: locals) v.wg ∧
      CreateDisposal.PendingBatch last ledger picked.items := by
  cases path with
  | intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ afterGuard pending => exact ⟨afterGuard,pending⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached
