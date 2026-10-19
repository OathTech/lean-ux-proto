import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedCreateCleanupAccounts

/-! Original refused-cleanup points include every ordered entry and both
native post-erase receipt intervals. Their evidence comes from the original
creation account, and their remainder is the literal original loop suffix. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.CreateCleanup
open Leanux Leanux.WG Leanux.Proofs.Logged TransmitSecurity CausalJournal
open AllocatedObligation CreateDisposal CompleteCarrier CreatePoints CreatePhase

theorem at_cursor (entry : Entry pid items w h ret q prior)
    (cursor : Cursor (.createRefused pid ret) items q prior skb rest u middle)
    (before : Accounted h ledger debts (⟨.unpublished,pid,items⟩::locals) w.wg)
    (pending : PendingBatch h ledger items) :
    ∃next done,Staged.Obligations.Step ledger next ∧ items=done++(skb::rest) ∧
      AllDropped middle next (.createRefused pid ret) done ∧ PendingBatch middle next (skb::rest) ∧
      Accounted middle next debts (⟨.unpublished,pid,skb::rest⟩::locals) u.wg := by
  obtain ⟨next,step,batch,account⟩:=entry.accounted before pending
  exact cursor.progress step (done:=[]) rfl (fun _ member=>False.elim (List.not_mem_nil member)) batch account

inductive Point (pid : PeerId) (items : List SkbId) (w : World) (h : List Event) :
    World → List Event → Prop where
  | entered (entry : Entry pid items w h ret v last) : Point pid items w h v last
  | cursor (entry : Entry pid items w h ret q prior)
      (path : Cursor (.createRefused pid ret) items q prior skb rest u middle) : Point pid items w h u middle
  | erased (entry : Entry pid items w h ret q prior)
      (path : Cursor (.createRefused pid ret) items q prior skb rest u middle)
      (native : (liftWG (freeTxSkb skb)).run u=.ok ((),v)) (phase : CleanupPrimitive.Phase) :
      Point pid items w h v (CleanupPrimitive.current phase u skb middle)

/-- Every declared cleanup point retains the same original ticket lineage.
The native erased-cell interval carries its actual pending receipt instead
of falsely retaining an account for the vanished cell. -/
theorem Point.evidence (point : Point pid items w h v last)
    (before : Accounted h ledger debts (⟨.unpublished,pid,items⟩::locals) w.wg)
    (pending : PendingBatch h ledger items) : CreatePhase.Evidence ledger debts locals pid items last v := by
  cases point with
  | @entered ret v last entry=>
    obtain ⟨next,step,batch,account⟩:=entry.accounted before pending
    exact .live (.cleanup next step (.createRefused pid ret) [] items rfl
      (fun _ member=>False.elim (List.not_mem_nil member)) batch account)
  | cursor entry path=>
    obtain ⟨next,done,step,ordered,settled,batch,account⟩:=at_cursor entry path before pending
    exact .live (.cleanup next step _ done _ ordered settled batch account)
  | erased entry path native phase=>
    rename_i ret q prior skb rest u middle
    obtain ⟨next,done,step,ordered,settled,batch,account⟩:=at_cursor entry path before pending
    obtain ⟨cut⟩:=free_cut (.createRefused pid ret) account batch
    rw [cut.native] at native
    have same : cut.after=_:=(Prod.mk.inj (Except.ok.inj native)).2
    exact same ▸ .awaiting next step _ done ordered settled cut phase

theorem Point.residual (point : Point pid items w h v last) :
    ∃remaining,runPrefix (CreatePoints.body pid items) w h=runPrefix remaining v last := by
  cases point with
  | entered entry=>exact ⟨_,entry.residual⟩
  | cursor entry path=>exact ⟨_,entry.residual.trans path.residual⟩
  | erased entry path native phase=>exact ⟨_,entry.residual.trans (path.pending_receipt native phase)⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.CreateCleanup
